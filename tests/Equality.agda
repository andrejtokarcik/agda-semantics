module Equality where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

_+_ : Nat -> Nat -> Nat
zero  + m = m
suc n + m = suc (n + m)

data Vec (A : Set) : Nat -> Set where
  []   : Vec A zero
  _::_ : {n : Nat} -> A -> Vec A n -> Vec A (suc n)

-- so that we know to parse
infixr 40 _::_

-- some hacks 'cuz we don't do pragmas
one : Nat
one = suc zero

two : Nat
two = suc (suc zero)

three : Nat
three = suc (suc (suc zero))

3things : Vec Nat three
3things = zero :: one :: zero :: []

3things' : Vec Nat (one + two)
3things' = 3things

-- getting boring aint it?
3things'' : Vec Nat (two + one)
3things'' = 3things'
