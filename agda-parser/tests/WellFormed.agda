module WellFormed where

data Nat : Set where
  zero : Nat
  succ : Nat -> Nat

postulate Vec : Set -> Nat -> Set
postulate _X_ : Set -> Set -> Set
postulate zip : {A B : Set} -> (n : Nat) -> Vec A n -> Vec B n -> Vec (A X B) n
