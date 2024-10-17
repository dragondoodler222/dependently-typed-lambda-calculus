module LambdaCalc where

import Debug.Trace


data Expr 
    = Var String -- pure variable 
    | Lambda String Expr Expr -- lambda term
    | Application Expr Expr -- variable application
    | Zero -- elementary natural 
    | Succ Expr -- successor of natural 
    | ElimNat Expr Expr Expr Expr -- induction 
    | Nat -- natural numbers :D
    | Fun String Expr Expr -- product types 
    | Star -- type of all types
    deriving (Show, Eq)

-- Context type
type Gamma = [(String, Expr)]

-- Alpha renaming variable generation
gen_variable :: String -> [String] -> String
gen_variable x used_vars
    | x `elem` used_vars = gen_variable (x ++ "'") used_vars
    | otherwise = x

-- Alpha rename a variable to avoid name clashes
alpha_rename :: Expr -> [String] -> Expr

-- rename any conflicting variables when bindings occur

alpha_rename (Lambda x type_x body) used_vars =
    let new_var = gen_variable x used_vars
        new_body = substitute x (Var new_var) body
    in Lambda new_var type_x (alpha_rename new_body (new_var : used_vars))

alpha_rename (Fun x type_x body) used_vars =
    let new_var = gen_variable x used_vars
        new_body = substitute x (Var new_var) body
    in Fun new_var type_x (alpha_rename new_body (new_var : used_vars))

-- propogate through all nonbinding expressions 

alpha_rename (Application e1 e2) used_vars = Application (alpha_rename e1 used_vars) (alpha_rename e2 used_vars)

alpha_rename (Succ x) used_vars = Succ (alpha_rename x used_vars)

alpha_rename (ElimNat e1 e2 e3 e4) used_vars = 
    ElimNat (alpha_rename e1 used_vars) (alpha_rename e2 used_vars) 
            (alpha_rename e3 used_vars) (alpha_rename e4 used_vars)

-- skip atomic expressions

alpha_rename expr _ = expr

-- Replace occurrences of string with expr in expr
substitute :: String -> Expr -> Expr -> Expr

-- If we see the variable we're replacing, terminate
substitute x s (Var y) = if x == y then s else Var y

-- If our variable name isn't being bound, continue replacing. Otherwise, ignore
substitute x s (Lambda y type_y body)
    | x == y = Lambda y (substitute x s type_y) body  
    | otherwise = Lambda y (substitute x s type_y) (substitute x s body)

substitute x s (Fun y type_y body)
    | x == y = Fun y (substitute x s type_y) body  
    | otherwise = Fun y (substitute x s type_y) (substitute x s body)

-- Propogate through nonbinding expressions

substitute x s (Application e1 e2) = Application (substitute x s e1) (substitute x s e2)

substitute x s (Succ e) = Succ (substitute x s e)

substitute x s (ElimNat e1 e2 e3 e4) = 
    ElimNat (substitute x s e1) (substitute x s e2) (substitute x s e3) (substitute x s e4)

-- Skip atomic expressions

substitute _ _ expr = expr  

-- Alpha convert before replacing string with expression

safe_replace :: Gamma -> String -> Expr -> Expr -> Either String Expr 

safe_replace ctx x arg body = do
    let free_vars_in_ctx = map fst ctx
    let renamed_body = alpha_rename body free_vars_in_ctx
    return $ substitute x arg renamed_body

-- Total reduction

reduce :: Gamma -> Expr -> Either String Expr

-- Eval-App + congruence rules

reduce ctx (Application e1 e2) = do
    e1' <- reduce ctx e1
    e2' <- reduce ctx e2
    case e1' of 
        Lambda x type_x body -> do 
            new_body <- safe_replace ctx x e2 body
            reduce ctx new_body
        _ -> Right $ Application e1' e2'

-- Eval-Succ

reduce ctx (Succ e) = do
    e' <- reduce ctx e
    return $ Succ e'

-- Eval-Lam-Body

reduce ctx (Lambda x y z) = do
    y' <- reduce ctx y
    z' <- reduce ((x, y') : ctx) z
    return $ (Lambda x y' z')

-- Eval-Prod-*

reduce ctx (Fun x y z) = do
    y' <- reduce ctx y
    z' <- reduce ((x, y') : ctx) z
    return $ (Fun x y' z')

-- Eval-ElimNat-0, succ + congruence rules

reduce ctx (ElimNat e1 e2 e3 e4) = do
    e1' <- reduce ctx e1
    e2' <- reduce ctx e2
    e3' <- reduce ctx e3
    e4' <- reduce ctx e4
    case e4' of 
        Zero -> Right e2'
        Succ e5 -> reduce ctx (Application (Application e3' e5) (ElimNat e1' e2' e3' e5))
        _ -> Right $ ElimNat e1' e2' e3' e4'

-- Ignore atomic terms

reduce _ expr = return expr

-- Get type out of context var

extract_type :: String -> Gamma -> Maybe Expr
extract_type x [] = Nothing
extract_type x ((y, type_y):context)
    | x == y = Just type_y
    | otherwise = extract_type x context

type_check :: Gamma -> Expr -> Either String Expr

-- Type-Var-Ref
type_check ctx (Var x) = case extract_type x ctx of 
    Just type_y -> Right type_y 
    Nothing -> Left $ "Error: Untyped Variable " ++ x ++ "."

-- Type-Lambda
type_check ctx (Lambda x type_x body) = do
    type_of_type <- type_check ctx type_x
    case type_of_type of
        Star -> do 
            red_type <- reduce ctx type_x -- Type-Eval (implicit)
            type_body <- type_check ((x, red_type) : ctx) body
            -- Ensure the function takes type type
            type_type_body <- type_check ctx type_body
            case type_type_body of
                Star -> Right (Fun x red_type type_body)
                _ -> Left $ "Error: Function of Non-Type Type " ++ (show type_body) ++ "."  
        _ -> Left $ "Error: Anonymous Function Given Type " ++ show type_of_type ++ "."

-- Type-App
type_check ctx (Application e1 e2) = do 
    type_head <- type_check ctx e1
    type_body <- type_check ctx e2
    case type_head of
        Fun x t1 t2 -> do
            new <- safe_replace ctx x e2 t2
            reduce ctx $ new
        _ -> Left $ "Error: Applying Non-Function Type " ++ (show type_head) ++ " to Argument."

-- Type-Zero
type_check ctx Zero = Right Nat

-- Type-Nat
type_check ctx Nat = Right Star

-- Type-Star
type_check ctx Star = Right Star

-- Type-Product
type_check ctx (Fun a x y) = Right Star

-- Type-Succ
type_check ctx (Succ x) = do
    type_x <- type_check ctx x
    case type_x of 
        Nat -> Right Nat
        _ -> Left $ "Error: Applying SUCC to object " ++ (show x) ++ " of type " ++ (show type_x) ++ "."

-- Type-Elim-Nat
type_check ctx (ElimNat e1 e2 e3 e4) = do
    type_e1 <- type_check ctx e1
    case type_e1 of 
        Fun x Nat Star -> do
            type_e4 <- type_check ctx e4
            case type_e4 of
                Nat -> reduce ctx (Application e1 e4)
                _ -> Left $ "Error: Expected Nat for ElimNat arg 4 but got " ++ (show type_e4) ++ "."
        _ -> Left $ "Error: Invalid Type " ++ (show type_e1) ++ " of ElimNat arg 1."
