module CH where

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

infixl 6 _+_
_+_ : ℕ → ℕ → ℕ
zero      + m  = m
(succ n)  + m  = succ (n + m)

infix 4 _≡_
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

{-
t1 : {n : ℕ} -> zero ≡ n
t1 = refl
-}

data _==_ {A : Set} : A → A → Set where
  refl' : (a : A) → a == a

sym : ∀ x y → x == y → y == x
sym .a .a (refl' a) = refl' a
