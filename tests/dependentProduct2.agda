module dependentProduct2 where


postulate A : Set
postulate B : A -> Set

data AB : Set where
  p : (a : A) -> B a -> AB

π0 : AB -> A
π0 (p a b) = a

π1 : (ab : AB) -> B (π0 ab)
π1 (p a b) = b

postulate a : A
postulate b : B a


ab : AB 
ab = p a b 



postulate ab' : AB

a' : A
a' = π0 ab'

b' : B a'
b' = π1 ab'


