module reflnat where


data ℕ : Set where
  Z : ℕ 
  S : ℕ -> ℕ 


_+_ : ℕ -> ℕ ->  ℕ
n + Z   = n
n + S m = S (n + m)

infixr 10 _+_

infixr 20 _*_
_*_ : ℕ -> ℕ ->  ℕ
n * Z   = Z
n * S m = n * m + n


data Bool : Set where
  tt : Bool
  ff : Bool

data ⊤ : Set where
  true : ⊤ 

data ⊥ : Set where


Atom : Bool -> Set
Atom tt = ⊤ 
Atom ff = ⊥ 

_==Bool_ : ℕ -> ℕ -> Bool
Z     ==Bool  Z     = tt
(S n) ==Bool  (S m) = n ==Bool m
_     ==Bool  _     = ff
-- Z     ==Bool (S _)  = ff
-- (S _) ==Bool Z      = ff


_==_ : ℕ -> ℕ -> Set
n == m = Atom ( n ==Bool m)


Refl : Set
Refl = (n : ℕ) -> n == n


refl : Refl
refl Z     = true
refl (S n) = refl n






