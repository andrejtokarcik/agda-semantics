-- https://github.com/bitonic/tog/wiki/Implicit-Arguments
-- aj s popisom checkingu od Andreasa Abela

module ImplArg where
data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

data Vec (A : Set) : Nat -> Set where
  vnil  : Vec A zero
  vcons : {n : Nat} -> A -> Vec A n -> Vec A (suc n)

Cons = {A : Set} (a : A) {n : Nat} -> Vec A n -> Vec A (suc n)

cons : Cons
cons a = vcons a
