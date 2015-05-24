module fib1 where

data ℕ : Set where
  Z : ℕ 
  S : ℕ -> ℕ 


_+_ : ℕ -> ℕ ->  ℕ
n + Z   = n
n + S m = S (n + m)

one : ℕ 
one = S Z

fib : ℕ -> ℕ
fib Z         = one
fib (S Z)     = one
fib (S (S n)) = fib n + fib (S n)
