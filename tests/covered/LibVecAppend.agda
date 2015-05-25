------------------------------------------------------------------------
-- The Agda standard library
--
-- Vectors
------------------------------------------------------------------------

module LibVecAppend where

data ℕ : Set where
  zero : ℕ
  suc : ℕ -> ℕ

data Fin : ℕ -> Set where
    fzero : {n : ℕ} -> Fin (suc n)
    fsuc : {n : ℕ} -> Fin n -> Fin (suc n)

_+_ : ℕ -> ℕ -> ℕ
zero + n = n
suc m + n = suc (m + n)

_*_ : ℕ -> ℕ -> ℕ
zero * _ = zero
suc m * n = n + (m * n)


infixr 5  _∷_
data List (A : Set) : Set where
  []  : List A
  _∷_ : (x : A) (xs : List A) → List A

{-
open import Category.Applicative
open import Data.Nat
open import Data.Fin using (Fin; zero; suc)
open import Data.List as List using (List)
open import Data.Product as Prod using (∃; ∃₂; _×_; _,_)
open import Function
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
-}

------------------------------------------------------------------------
-- Types

infixr 5 _,_

data Vec (A : Set) : ℕ → Set where
  <>  : Vec A zero
  _,_ : ∀ {n} (x : A) (xs : Vec A n) → Vec A (suc n)

------------------------------------------------------------------------
-- Some operations

{-
head : ∀ {n} {A : Set} → Vec A (suc n) → A
head (x , xs) = x

tail : ∀ {n} {A : Set} → Vec A (suc n) → Vec A n
tail (x , xs) = xs
-}

<_> : ∀ {A : Set} → A → Vec A (suc zero)
< x > = x , <>


{-
 Vect A n → Vect A m → Vect A (m + n)
append vnil ys = ys
append (vcons x xs) ys = vcons x (append xs ys)
-}

infixr 5 _++_

_++_ : ∀ {m n} {A : Set} → Vec A m → Vec A n → Vec A (m + n)
<>       ++ ys = ys
(x , xs) ++ ys = x , (xs ++ ys)


t1 : Vec ℕ (suc zero)
t1 = < zero > ++ <>

{-
infixl 4 _⊛_

_⊛_ : ∀ {b n} {A : Set} {B : Set} →
      Vec (A → B) n → Vec A n → Vec B n
<>       ⊛ _        = <>
(f , fs) ⊛ (x , xs) = f x , (fs ⊛ xs)
-}

{-
replicate : ∀ {n} {A : Set} → A → Vec A n
replicate {n = zero}  x = <>
replicate {n = suc n} x = x , replicate x
-}

replicate : ∀ {n} {A : Set} → A → Vec A n
replicate {zero}  x = <>
replicate {suc n} x = x , replicate x

{-
applicative : ∀ {n} → RawApplicative (λ (A : Set) → Vec A n)
applicative = record
  { pure = replicate
  ; _⊛_  = _⊛_
  }
-}

{-
map : ∀ {n} {A : Set} {B : Set} →
      (A → B) → Vec A n → Vec B n
map f xs = replicate f ⊛ xs

zipWith : ∀ {n} {A : Set} {B : Set} {C : Set} →
          (A → B → C) → Vec A n → Vec B n → Vec C n
zipWith _⊕_ xs ys = replicate _⊕_ ⊛ xs ⊛ ys
-}

{-
zip : ∀ {n} {A : Set} {B : Set} →
      Vec A n → Vec B n → Vec (A × B) n
zip = zipWith _,_

unzip : ∀ {a b n} {A : Set} {B : Set} →
        Vec (A × B) n → Vec A n × Vec B n
unzip <>              = <> , <>
unzip ((x , y) , xys) = Prod.map (_,_ x) (_,_ y) (unzip xys)
-}

{-
foldr : ∀ {a b} {A : Set} (B : ℕ → Set) {m} →
        (∀ {n} → A → B n → B (suc n)) →
        B zero →
        Vec A m → B m
foldr b _⊕_ n <>       = n
foldr b _⊕_ n (x , xs) = x ⊕ foldr b _⊕_ n xs

foldr₁ : ∀ {A : Set} {m} →
         (A → A → A) → Vec A (suc m) → A
foldr₁ _⊕_ (x , <>)     = x
foldr₁ _⊕_ (x , y , ys) = x ⊕ foldr₁ _⊕_ (y , ys)

foldl : ∀ {a b} {A : Set} (B : ℕ → Set) {m} →
        (∀ {n} → B n → A → B (suc n)) →
        B zero →
        Vec A m → B m
foldl b _⊕_ n <>       = n
foldl b _⊕_ n (x , xs) = foldl (λ n → b (suc n)) _⊕_ (n ⊕ x) xs

foldl₁ : ∀ {A : Set} {m} →
         (A → A → A) → Vec A (suc m) → A
foldl₁ _⊕_ (x , xs) = foldl _ _⊕_ x xs

concat : ∀ {a m n} {A : Set} →
         Vec (Vec A m) n → Vec A (n * m)
concat <>         = <>
concat (xs , xss) = xs ++ concat xss

{-
splitAt : ∀ {A : Set} m {n} (xs : Vec A (m + n)) →
          ∃₂ λ (ys : Vec A m) (zs : Vec A n) → xs ≡ ys ++ zs
splitAt zero    xs                = (<> , xs , refl)
splitAt (suc m) (x , xs)          with splitAt m xs
splitAt (suc m) (x , .(ys ++ zs)) | (ys , zs , refl) =
  ((x , ys) , zs , refl)


take : ∀ {A : Set} m {n} → Vec A (m + n) → Vec A m
take m xs          with splitAt m xs
take m .(ys ++ zs) | (ys , zs , refl) = ys

drop : ∀ {A : Set} m {n} → Vec A (m + n) → Vec A n
drop m xs          with splitAt m xs
drop m .(ys ++ zs) | (ys , zs , refl) = zs

group : ∀ {A : Set} n k (xs : Vec A (n * k)) →
        ∃ λ (xss : Vec (Vec A k) n) → xs ≡ concat xss
group zero    k <>                  = (<> , refl)
group (suc n) k xs                  with splitAt k xs
group (suc n) k .(ys ++ zs)         | (ys , zs , refl) with group n k zs
group (suc n) k .(ys ++ concat zss) | (ys , ._ , refl) | (zss , refl) =
  ((ys , zss) , refl)

-- Splits a vector into two "halves".

split : ∀ {a n} {A : Set} → Vec A n → Vec A ⌈ n /2⌉ × Vec A ⌊ n /2⌋
split <>           = (<>     , <>)
split (x , <>)     = (x , <> , <>)
split (x , y , xs) = Prod.map (_,_ x) (_,_ y) (split xs)
-}

{-
reverse : ∀ {n} {A : Set} → Vec A n → Vec A n
reverse {A = A} = foldl (Vec A) (λ rev x → x , rev) <>
-}

sum : ∀ {n} → Vec ℕ n → ℕ
sum = foldr _ _+_ zero

toList : ∀ {n} {A : Set} → Vec A n → List A
toList <>       = List.[]
toList (x , xs) = List._∷_ x (toList xs)

{-
fromList : ∀ {A : Set} → (xs : List A) → Vec A (List.length xs)
fromList List.<>         = <>
fromList (List._,_ x xs) = x , fromList xs
-}

-- Snoc.

infixl 5 _,ʳ_

_,ʳ_ : ∀ {n} {A : Set} → Vec A n → A → Vec A (suc n)
<>       ,ʳ y = < y >
(x , xs) ,ʳ y = x , (xs ,ʳ y)

{-
initLast : ∀ {a n} {A : Set} (xs : Vec A (1 + n)) →
           ∃₂ λ (ys : Vec A n) (y : A) → xs ≡ ys ,ʳ y
initLast {n = zero}  (x , <>)         = (<> , x , refl)
initLast {n = suc n} (x , xs)         with initLast xs
initLast {n = suc n} (x , .(ys ,ʳ y)) | (ys , y , refl) =
  ((x , ys) , y , refl)

init : ∀ {n} {A : Set} → Vec A (1 + n) → Vec A n
init xs         with initLast xs
init .(ys ,ʳ y) | (ys , y , refl) = ys

last : ∀ {n} {A : Set} → Vec A (1 + n) → A
last xs         with initLast xs
last .(ys ,ʳ y) | (ys , y , refl) = y
-}

infixl 1 _>>=_

_>>=_ : ∀ {a b m n} {A : Set} {B : Set} →
        Vec A m → (A → Vec B n) → Vec B (m * n)
xs >>= f = concat (map f xs)

infixl 4 _⊛*_

_⊛*_ : ∀ {a b m n} {A : Set} {B : Set} →
       Vec (A → B) m → Vec A n → Vec B (m * n)
fs ⊛* xs = fs >>= λ f → map f xs

-- Interleaves the two vectors.

{-
infixr 5 _⋎_

_⋎_ : ∀ {m n} {A : Set} →
      Vec A m → Vec A n → Vec A (m +⋎ n)
<>       ⋎ ys = ys
(x , xs) ⋎ ys = x , (ys ⋎ xs)
-}

-- A lookup function.

lookup : ∀ {a n} {A : Set} → Fin n → Vec A n → A
lookup fzero    (x , xs) = x
lookup (fsuc i) (x , xs) = lookup i xs

-- An inverse of flip lookup.

{-
tabulate : ∀ {n a} {A : Set} → (Fin n → A) → Vec A n
tabulate {zero}  f = <>
tabulate {suc n} f = f zero , tabulate (f ∘ suc)
-}

-- Update.

infixl 6 _[_]≔_

_[_]≔_ : ∀ {a n} {A : Set} → Vec A n → Fin n → A → Vec A n
<>       [ ()    ]≔ y
(x , xs) [ fzero  ]≔ y = y , xs
(x , xs) [ fsuc i ]≔ y = x , xs [ i ]≔ y

-- Generates a vector containing all elements in Fin n. This function
-- is not placed in Data.Fin because Data.Vec depends on Data.Fin.
--
-- The implementation was suggested by Conor McBride ("Fwd: how to
-- count 0..n-1", http://thread.gmane.org/gmane.comp.lang.agda/2554).

{-
allFin : ∀ n → Vec (Fin n) n
allFin _ = tabulate id
-}

-}
