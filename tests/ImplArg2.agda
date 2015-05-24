module ImplArg2 where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

data Vec (A : Set) : Nat -> Set where
  vnil  : Vec A zero
  vcons : {n : Nat} -> A -> Vec A n -> Vec A (suc n)

cons : {A : Set} (a : A) {n : Nat} -> Vec A n -> Vec A (suc n)
cons a = vcons a
