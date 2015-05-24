module Fin where

data Nat : Set where
  zero : Nat
  succ : Nat -> Nat

data Fin : Nat -> Set where
    fzero : {n : Nat} -> Fin (succ n)
    fsucc : {n : Nat} -> Fin n -> Fin (succ n)
