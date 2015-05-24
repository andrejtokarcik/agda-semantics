
module ListNat where
  data Nat : Set where
    zero : Nat
    succ : Nat -> Nat

  data List (a : Set) : Set where
    []   : List a
    _::_ : a -> List a -> List a

  infixr 30 _::_

  [1,0,2] = one :: zero :: succ one :: []
    where one = succ zero
