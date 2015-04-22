module Id where

{-
postulate x : Set
postulate y : Set
postulate _p_ : Set -> Set -> Set

e : Set
e = x p y
-}

{-
id2 : (A : Set0) -> (_ : A) -> A
id2 = \ (C : Set) (z : C) -> z
-}

{-
id : (A : Set) -> A -> A
id = \ A x -> x
-}

{-
idImp : {A : Set} -> A -> A
idImp = \ {A} x -> x
-}

id : (A : Set) -> A -> A
id A x = x
