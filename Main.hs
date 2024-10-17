module Main where

import LambdaCalc

import Debug.Trace 

-- We follow stdlib.agda

-- Iterative definitions on the naturals
iterNat = (Lambda "A" Star 
    (Lambda "z" (Var "A") 
        (Lambda "s" (Fun "_" (Var "A") (Var "A"))
            (Lambda "n" Nat (
                ElimNat (Lambda "_1" Nat (Var "A")) (Var "z") (Lambda "_1" Nat (Var "s")) (Var "n")
            ))))) 

-- The type of x =_Nat y
same = (Lambda "A" Star 
        (Lambda "a" (Var "A") 
            (Lambda "b" (Var "A")
                (Fun "P"
                    (Fun "_" (Var "A") Star)
                    (Fun "z" (Application (Var "P") (Var "a"))
                        (Application (Var "P") (Var "b"))
                    )
                )
            )
        )
    )

-- Reflexive element of x =_Nat x
refl = (Lambda "A" Star (
    (Lambda "x" (Var "A") 
        (Lambda "P" (Fun "_" (Var "A") Star)
            (Lambda "z" (Application (Var "P") (Var "x"))
                 (Var "z")
                )

            )
        )
    ))

-- Transitivity of equality
trans = (Lambda "A" Star
    (Lambda "x" (Var "A")
        (Lambda "y" (Var "A")
            (Lambda "z" (Var "A")
                    (Lambda "pxy" (Application (Application (Application same (Var "A")) (Var "x")) (Var "y"))
                        (Lambda "pyz" (Application (Application (Application same (Var "A")) (Var "y")) (Var "z"))
                            (Lambda "P" (Fun "_" (Var "A") Star)
                                (Lambda "px" (Application (Var "P") (Var "x"))
                                    $ Application (Application (Var "pyz") (Var "P")) (Application (Application (Var "pxy") (Var "P")) (Var "px"))
                                )
                            )
                        )
                    )
                )
            )

        )
    )

-- Addition defined
plus = (Lambda "x" Nat (Lambda "y" Nat $ 
    (Application (Application (Application (Application iterNat Nat) (Var "y")) (Lambda "." Nat (Succ (Var ".")))) (Var "x"))
    ))

-- Proof that if x = y, then succ x = succ
same_under_suc = 
    Lambda "x" Nat
        (Lambda "y" Nat
            (Lambda "xy_eq" (Application (Application (Application same Nat) (Var "x")) (Var "y"))
                (Lambda "P" (Fun "z" Nat Star)
                    (Application (Var "xy_eq")
                        (Lambda "z1" Nat
                            (Application (Var "P") (Succ (Var "z1")))
                        )
                    )
                )
            )
        )

-- Proof that x == x + 0
plus_right_zero = 
    Lambda "x" Nat
        (ElimNat
            (Lambda "x" Nat (Application (Application (Application same Nat) (Var "x")) (Application (Application plus (Var "x")) Zero)))
            (Lambda "P" (Fun "_1" Nat Star) (Lambda "x2" Nat (Var "x2"))) 
            (Lambda "n" Nat
                (Lambda "x1" (Fun "_" (Fun "_2" Nat Star) Nat)
                    (Lambda "P" (Fun "_1" Nat Star)
                        (Application (Var "x1") (Lambda "z" Nat (Application (Var "P") (Succ (Var "z")))))  
                    )
                )
            )
            (Var "x")
        )

-- Proof that x + (y + 1) == 1 + x + y
plus_right_suc = Lambda "x" Nat ( Lambda "y" Nat ( ElimNat
	(Lambda "x" Nat (Application (Application (Application same Nat) (Succ (Application (Application plus (Var "x")) (Var "y")))) (Application (Application plus (Var "x")) (Succ (Var "y")))))
	(Lambda "P" (Fun "_1" Nat Star) (Lambda "x2" Nat (Var "x2"))) 
	(Lambda "n" Nat
        (Lambda "x1" (Fun "_" (Fun "_2" Nat Star) Nat)
            (Lambda "P" (Fun "_1" Nat Star)
                (Application (Var "x1") (Lambda "z" Nat (Application (Var "P") (Succ (Var "z")))))  
            )
        )
    )
	(Var "x")
	))  

-- And finally, the commutativity of addition
plus_comm = Lambda "x" Nat ( Lambda "y" Nat ( ElimNat
	(Lambda "x" Nat (Application (Application (Application same Nat) (Application (Application plus (Var "x")) (Var "y"))) (Application (Application plus (Var "y")) (Var "x"))))
	(Application plus_right_zero (Var "y"))
	(Lambda "n" Nat
        (Lambda "p"
        	(Application (Application (Application same Nat) (Application (Application plus (Var "n")) (Var "y")) ) (Application (Application plus (Var "y")) (Var "n")) )
		    (Application
		        (Application
		        	(Application
			        	(Application
				        	(Application  
				        		(Application trans Nat)
				        		(Succ (Application (Application plus (Var "n")) (Var "y")))
			        		)
			        		(Succ (Application (Application plus (Var "y")) (Var "n")))
				        )
				        (Application (Application plus (Var "y")) (Succ (Var "n")))
			        )
		        	(Application (Application (Application same_under_suc (Application (Application plus (Var "n")) (Var "y"))) (Application (Application plus (Var "y")) (Var "n"))) (Var "p"))
		        )
		    (Application (Application plus_right_suc (Var "y")) (Var "n"))
		    )
        ) 
    )
	(Var "x")
	))

-- Integer multiplication
mul = 
    Lambda "n" Nat (Lambda "m" Nat 
        (ElimNat 
            (Lambda "_" Nat Nat)  
            Zero                  
            (Lambda "x" Nat (Lambda "acc" Nat (Application (Application plus (Var "n")) (Var "acc")))) 
            (Var "m")   
        )
    )

-- Polymorphic Identity Function
polyId = (Lambda "A" Star (Lambda "x" (Var "A") (Var "x")))



-- These, beautifully, are equal.
test = (Application (Application plus_comm (Succ Zero)) (Succ (Succ Zero)))
reflthree = (Application (Application refl Nat) (Succ (Succ (Succ Zero))))



main :: IO ()

main = putStrLn $ case reduce [] $ reflthree of 
    Right x -> trace (show x) $ show $ type_check [] x
    Left y -> y
