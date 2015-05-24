module MetaId where

  data Nat : Set where
    zero : Nat
    suc  : Nat -> Nat

  expr = (\ (a : Set) (x : a) -> x) _ zero
