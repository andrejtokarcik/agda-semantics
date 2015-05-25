
module List where

  data List (a : Set) : Set where
    nil  : List a
    _::_ : a -> List a -> List a

  nil2 : (\x -> x) ({a : Set} -> List a)
  nil2 = nil {_}

  tt : Set1 -> Set2
  tt _ = Set1

  map : {a b : Set} -> (a -> b) -> List a -> List b
  map f nil       = nil
  map f (x :: xs) = f x :: map f xs
