module Id where

{-
postulate x : Set
postulate y : Set
postulate _p_ : Set -> Set -> Set

e : Set
e = x p y
-}

id2 : (A : Set) -> (e : A) -> A
id2 = \ A x -> x
