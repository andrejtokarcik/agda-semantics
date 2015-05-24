module 015-logic where

-- Simple propositional logic.

data False : Set where

-- Logical and. We represent a proof of A and B as a pair of proofs,
-- namely, a proof of A and a proof of B.

data Pair (A B : Set) : Set where
  _,_ : A -> B -> Pair A B

_∧_ : (A B : Set) -> Set
A ∧ B = Pair A B

-- Get back proof of any of the components.

a∧b->a : {A B : Set} -> A ∧ B -> A
a∧b->a (a , b) = a 

a∧b->b : {A B : Set} -> A ∧ B -> B
a∧b->b (a , b) = b

-- Logical or. We represent a proof of A or B as a proof of A or a
-- proof of B.

data Either (A B : Set) : Set where
  left : A -> Either A B
  right : B -> Either A B

_∨_ : (A B : Set) -> Set
A ∨ B = Either A B

-- Negation.

¬_ : (A : Set) -> Set
¬ A = A -> False

-- Now some properties.

-- Commutativity.

a∧b->b∧a : ∀ {A B} -> A ∧ B -> B ∧ A
a∧b->b∧a ( a , b ) = ( b , a )

a∨b->b∨a : ∀ {A B} -> A ∨ B -> B ∨ A
a∨b->b∨a (left a) = right a
a∨b->b∨a (right b) = left b

-- Distributivity.

a∧[b∨c]->[a∧b]∨[a∧c] : ∀ {A B C} -> A ∧ (B ∨ C) -> (A ∧ B) ∨ (A ∧ C)
a∧[b∨c]->[a∧b]∨[a∧c] (a , left b) = left (a , b)
a∧[b∨c]->[a∧b]∨[a∧c] (a , right c) = right (a , c)

[a∧b]∨[a∧c]->a∧[b∨c] : ∀ {A B C} -> (A ∧ B) ∨ (A ∧ C) -> A ∧ (B ∨ C)
[a∧b]∨[a∧c]->a∧[b∨c] (left (a , b)) = (a , left b)
[a∧b]∨[a∧c]->a∧[b∨c] (right (a , c)) = (a , right c)

a∨[b∧c]->[a∨b]∧[a∨c] : ∀ {A B C} -> A ∨ (B ∧ C) -> (A ∨ B) ∧ (A ∨ C)
a∨[b∧c]->[a∨b]∧[a∨c] (left a) = (left a , left a)
a∨[b∧c]->[a∨b]∧[a∨c] (right (b , c)) = (right b , right c)

[a∨b]∧[a∨c]->a∨[b∧c] : ∀ {A B C} -> (A ∨ B) ∧ (A ∨ C) -> A ∨ (B ∧ C)
[a∨b]∧[a∨c]->a∨[b∧c] ( left a , _ ) = left a
[a∨b]∧[a∨c]->a∨[b∧c] ( _ , left a ) = left a
[a∨b]∧[a∨c]->a∨[b∧c] ( right b , right c ) = right (b , c)

-- Contraposition.

[a->b]->[¬b->¬a] : ∀ {A B} -> (A -> B) -> (¬ B -> ¬ A)
[a->b]->[¬b->¬a] a->b ¬b a = ¬b (a->b a)

-- Contradiction.

¬[a∧¬a] : ∀ {A} -> ¬ (A ∧ (¬ A))
¬[a∧¬a] ( a , ¬a ) = ¬a a

-- De Morgan.

¬[a∨b]->¬a∧¬b : ∀ {A B} -> ¬ (A ∨ B) -> (¬ A) ∧ (¬ B)
¬[a∨b]->¬a∧¬b ¬[a∨b] = (\a -> ¬[a∨b] (left a)) , (\b -> ¬[a∨b] (right b))

¬a∧¬b->¬[a∨b] : ∀ {A B} -> (¬ A) ∧ (¬ B) -> ¬ (A ∨ B)
¬a∧¬b->¬[a∨b] ( ¬a , ¬b ) (left a) =  ¬a a
¬a∧¬b->¬[a∨b] ( ¬a , ¬b ) (right b) =  ¬b b

¬a∨¬b->¬[a∧b] : ∀ {A B} -> (¬ A) ∨ (¬ B) -> ¬ (A ∧ B)
¬a∨¬b->¬[a∧b] (left ¬a) ( a , b ) = ¬a a
¬a∨¬b->¬[a∧b] (right ¬b) ( a , b ) = ¬b b

-- not provable, see https://math.stackexchange.com/questions/120187/does-de-morgans-laws-hold-in-propositional-intuitionistic-logic
-- ¬[a∧b]->¬a∨¬b : ∀ {A B} -> ¬ (A ∧ B) -> (¬ A) ∨ (¬ B)
-- ¬[a∧b]->¬a∨¬b ¬[a∧b] = {!!}
