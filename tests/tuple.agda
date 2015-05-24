module tuple where


data ℕ : Set where
  Z : ℕ 
  S : ℕ -> ℕ 


_+_ : ℕ -> ℕ ->  ℕ
n + Z   = n
n + S m = S (n + m)

infixr 30 _+_


data Nil : Set where
  [] : Nil


infix 20 _::_

data Cons (A B : Set) : Set where
  _::_ : A -> B -> Cons A B 


Tuple : Set -> ℕ -> Set
Tuple A Z     = Nil
Tuple A (S n) = Cons A (Tuple A n)


sumℕTuple : {n : ℕ} -> Tuple ℕ n -> Tuple ℕ n -> Tuple ℕ n
sumℕTuple {Z} []       []         = []
sumℕTuple {S n} (m :: l) (m' :: l') 
            = m + m' :: (sumℕTuple l l')




