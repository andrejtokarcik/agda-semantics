module reductionSystems1 where


data ℕ : Set where 
  Z : ℕ  
  S : ℕ -> ℕ

_+_ : ℕ -> ℕ -> ℕ
n + Z   = n
n + S m = S (n + m)

_*_ : ℕ -> ℕ -> ℕ
n * Z = Z
n * S m = (n * m) + n


{-
{-# BUILTIN NATURAL  ℕ  #-}
{-# BUILTIN ZERO     Z #-}
{-# BUILTIN SUC      S  #-}
{-# BUILTIN NATPLUS  _+_  #-}
{-# BUILTIN NATTIMES _*_  #-}
-}
