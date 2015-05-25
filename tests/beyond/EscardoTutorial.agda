-- A brief Agda tutorial.
-- Martín Escardó, 7 Sep 2012 (updated to be compatible with Agda 2.4.2 2 Oct 2014).
--
-- Agda is a computer-implemented dialect of Martin-Löf type theory.
-- It can both check and run proofs. 
--
-- Propositions are types (also called sets, indicated by the keyword
-- Set), and their witnesses or proofs are programs.
--
-- If one ignores this view/encoding of propositions, Agda is simply a
-- strongly typed, pure, functional programming language with
-- dependent types and other kinds of fancy types.
--
-- All programs normalize in Agda. 
---
-- Gödel's system T is included in Agda, but Platek-Scott-Plotkin's
-- PCF is not.  But Agda is much more expressive than system T: it
-- defines many more functions ℕ → ℕ, for example, and encodes much
-- higher ordinals.

-- The Agda wiki http://wiki.portal.chalmers.se/agda/agda.php tells
-- you how to install Agda and get started with editing.
--
-- I recommend the tutorial paper 
---    http://www.cse.chalmers.se/~ulfn/papers/afp08/tutorial.pdf,
-- among others available at 
--     http://wiki.portal.chalmers.se/agda/agda.php?n=Main.Documentation
--
-- See also the standard library
--     http://www.cse.chalmers.se/~nad/listings/lib-0.6/README.html
-- which we will not use in this tutorial.

module EscardoTutorial where

-- An inductive definition:

data ℕ : Set where
 zero : ℕ
 succ : ℕ → ℕ

-- This notation uses unicode UTF-8. To enter unicode characters in emacs in Agda mode, see 
-- http://wiki.portal.chalmers.se/agda/agda.php?n=Main.QuickGuideToEditingTypeCheckingAndCompilingAgdaCode
-- (usually LaTeX syntax works).

-- Could instead write the following, which is equivalent with a
-- different notation, using ascii characters only:

data N : Set where
 zero : N
 succ : N -> N
 one  : N

-- But we will use the first definition. (Later we may prove that ℕ
-- and N are isomorphic, as an exercise.)

-- Our first function, inductively defined:

_+_ : ℕ → ℕ → ℕ
x + zero = x
x + succ y = succ(x + y)

-- We can define a simple-recursion combinator:

rec : (X : Set) → X → (X → X) → (ℕ → X)
rec X x f zero = x
rec X x f (succ n) = f(rec X x f n)

-- Or the primitive-recursion combinator:

prim-rec : (X : Set) → X → (ℕ → X → X) → ℕ → X 
prim-rec X x f zero = x
prim-rec X x f (succ n) = f n (prim-rec X x f n)

-- Addition can then be instead defined as:

_+₁_ : ℕ → ℕ → ℕ
x +₁ y = rec ℕ x succ y

-- We are using a subscript to indicate a different version. An
-- identifier is a sequence of unicode (UTF-8 encoding) characters not
-- containing white space or reserved characters @.(){};_. 
-- 
-- Quoting from the agda wiki,
-- http://wiki.portal.chalmers.se/agda/pmwiki.php?n=ReferenceManual.LexicalMatters:
--
-- Furthermore, the following set of reserved words cannot be used as name parts.
--
-- ->         :         =        ?        \           |          →         ∀   --     λ
-- abstract   data      forall   hiding   import      in         infix     infixl   infixr
-- let        module    mutual   open     postulate   primitive  private   public   record
-- renaming   rewrite   using    where    with
-- Prop       Set[0–9]* [0–9]+
--
-- This means that strings like x:A and A→B are valid names. To write
-- the type signature and the function type, white space have to be
-- inserted: x : A, and A → B.
--

-- To illustrate some features, another equivalent definition is this:

rec₁ : (X : Set) → X → (X → X) → (ℕ → X)
rec₁ X x f = h
 where 
  h : ℕ → X
  h zero = x
  h (succ n) = f(h n)

-- Indentation matters.

-- The parameter X of the definition of rec/rec₁ may be made implicit,
-- and this is sensible:

rec₂ : {X : Set} → X → (X → X) → (ℕ → X)
rec₂ {X} x f = h
 where 
  h : ℕ → X
  h zero = x
  h (succ n) = f(h n)

-- Now we can define addition omitting the type ℕ:

_+₂_ : ℕ → ℕ → ℕ
x +₂ y = rec₂ x succ y

-- Agda then infers (by unification) that this is the only possibly
-- choice for the implicit argument. 

-- In cases when the inference fails, or when you want to implicitly
-- supply the implicit parameter for emphasis, you can write:

_+₃_ : ℕ → ℕ → ℕ
x +₃ y = rec₂ {ℕ} x succ y

-- You can also write:

_+₄_ : ℕ → ℕ → ℕ
_+₄_ x y = rec₂ {ℕ} x succ y

-- or even, using η-contraction:

_+₅_ : ℕ → ℕ → ℕ
_+₅_ x = rec₂ {ℕ} x succ

-- or:

_+₆_ : ℕ → ℕ → ℕ
_+₆_ = λ x → rec₂ {ℕ} x succ

-- or, using only ascii characters:

_+₇_ : ℕ → ℕ → ℕ
_+₇_ = \x -> rec₂ {ℕ} x succ

-- I prefer the original definition.

-- You can also declare an associativity and precedence for (the
-- various versions of) _+_ if you wish (valid from now on):

infixl 5 _+_

-- Since we are discussing syntax, let also do:

-- {-# BUILTIN NATURAL ℕ #-}
{-# BUILTIN NATURAL N #-}

-- This allows you to write e.g. 0 to mean zero and 3 to mean
-- Succ(Succ(Succ zero)).

-- So far we have a few definitions. We want to prove something about
-- them.


-- Agda uses the Brouwer-Heyting-Kolmogorov-Curry-Howard
-- representation of propositions as types. 
-- 
-- Types are called sets in Agda syntax, with the keyword "Set". 
-- (And in the early accounts by Martin-Löf too.)
--
-- So a proposition is a set.
--
--    * A set may be empty: this represents "false".
--
--    * Or it may have an element: any inhabited set represents "true".
--
-- So a proposition may be true in many ways: an element of its
-- representing set is called a "witness" or a "realizer" or "a
-- proof".
--
--
-- A predicate on a type X is a function A : X → Set.  
-- For each element x : X it gives a set A x representing a
-- proposition.
--
--
-- * The BHKCH intepretation of implication:
--
--     A realizer of the proposition "A implies B" is a function that
--     given any realizer of A produces a realizer of B.
--  
--     Thus, the function type (A → B), built-in in Martin-Löf theory
--     and in Agda, codes implication.
--
--
-- * The BHKCH intepretation of universal quantification:
--
--     A realizer of "for all x in X, A x" is a function that
--     transforms any x in X into a realizer of A x.
--
--     The interpretation of universal quantification is given by
--     dependent products, again built-in in Martin-Löf theory and in
--     Agda.
--
--     In Martin-Löf type theory, it is written Π.  In Agda, the
--     notation (x : X) → A x is used, where A : X → Set.
--
--     It is the type of functions that map any x : X to an element y : A x.
--     Notice that the type of the output depends on the input.
--
--     Agda allows you to write ∀(x : X) → A x to mean (x : X) → A x.
--     When types can be inferred by Agda, you can also write ∀ x → A x.
--
-- * The BHKCH intepretation of existential quantification:
--
--     A realizer of "there is x in X s.t. A x" is a pair (x , a)
--     where x is in X and a is a realizer of A x.
--
--     In Martin-Löf type theory, Σ is used to define the
--     interpretation of existential quantification.
--
--     In Agda we need to (inductively) define it ourselves:

data Σ {X : Set} (A : X → Set) : Set where
     _,_ : (x₀ : X) → A x₀ → Σ \(x : X) → A x

-- Read Σ \(x : X) → A x as the sum of the sets A x for x : X.  Agda
-- is "intensional", but it uses the η rule.  So Σ \(x : X) → A x is
-- the same as Σ {X} A, because A is the same thing as \(x : X) → A x,
-- and because X can be inferred now, as it is given in the definition
-- \(x : X) → A x.

π₀ : {X : Set} {A : X → Set} → (Σ \(x : X) → A x) → X
π₀(x , a) = x

π₁ : {X : Set} {A : X → Set} → (z : Σ \(x : X) → A x) → A(π₀ z)
π₁(x , a) = a

-- Martin-Löf instead works with the following elimination rule, which
-- is a dependently type version of "uncurrying":

Σ-elim : {X : Set} → {Y : X → Set} → 
         {A : (Σ \(x : X) → Y x) → Set}

   → (∀(x : X) → ∀(y : Y x) → A(x , y))
   → ∀(t : (Σ \(x : X) → Y x)) → A t

Σ-elim f(x , y) = f x y

-- Notice that Σ-elim defines the projections:

π₀' : {X : Set} {A : X → Set} → (Σ \(x : X) → A x) → X
π₀' = Σ-elim (λ x a → x) 

π₁' : {X : Set} {A : X → Set} → (z : Σ \(x : X) → A x) → A(π₀ z)
π₁' = Σ-elim (λ x a → a) 

-- The converse holds if we assume "surjective-pairing", a form of the
-- η-rule for sums. Now this may be confusing: the way we defined Σ
-- using "data" doesn't give you that. But if you define Σ using a
-- record, then you do get that. See
-- http://www.cs.bham.ac.uk/~mhe/agda/SetsAndFunctions.html

-- Cartesian products are a special case of dependent sums, where Y
-- doesn't depend on x : X, which represent conjunctions in the BHKCH
-- interpretation of logic:

_×_ : Set → Set → Set
X × Y = Σ \(x : X) → Y

-- It is also useful to introduce ∃-notation:

∃ : {X : Set} → (A : X → Set) → Set
∃ = Σ

-- We have developed enough material to be able to formulate and prove
-- our first theorem: the Axiom of Choice:


AC : {X Y : Set} {A : X → Y → Set} →

 (∀(x : X) → ∃ \(y : Y) → A x y) → ∃ \(f : X → Y) → ∀(x : X) → A x (f x)

AC g = (λ x → π₀(g x)) , (λ x → π₁(g x))

-- We have a dependently typed version as well (not to be confused
-- with dependent choice, which I will discuss later), with the same
-- proof:

AC' : {X : Set} {Y : X → Set} {A : (x : X) → Y x → Set} →

 (∀(x : X) → ∃ \(y : Y x) → A x y) → ∃ \(f : ((x : X) → Y x)) → ∀(x : X) → A x (f x)

AC' g = ((λ x → π₀(g x)) , (λ x → π₁(g x)))

-- I find the following use of an implicit argument useful in order
-- to achieve a notation close to Martin-Löf's.

Π : {X : Set} → (Y : X → Set) → Set
Π {X} Y = (x : X) → Y x

-- For example the axiom of choice becomes less surprising when we
-- realize that it amounts to

AC-in-ML-notation : {X : Set} {Y : X → Set} {A : (x : X) → Y x → Set} →

 (Π \(x : X) → Σ \(y : Y x) → A x y) → Σ \(f : ((x : X) → Y x)) → Π \(x : X) → A x (f x)

AC-in-ML-notation g = ((λ x → π₀(g x)) , (λ x → π₁(g x)))

-- (The axiom of choice usually fails in a topos, but the above always
-- holds. In fact, the function AC-in-ML-notation is a
-- (pointwise) isomorphism. Exercise: define its inverse in Agda.)


-- Let's return to the natural numbers. 
-- We can also write an induction combinator:

induction : {A : ℕ → Set} → 

 A zero → (∀(k : ℕ) → A k → A(succ k)) → ∀(n : ℕ) → A n 

induction base step 0 = base
induction base step (succ n) = step n (induction base step n)

-- Notice that the realizer of the principle of induction has the same
-- definition as primitive recursion. Only the types are different:
-- that of primitive recursion is less general, and that of induction
-- is the dependent-type generalization.

prim-rec' : {X : Set} → X → (ℕ → X → X) → ℕ → X 
prim-rec' = induction

-- The empty type, representing the false proposition. 

data ∅ : Set where
 -- no constructors given

-- The "elimintation rule of false", or "ex-falso quod libet", or the
-- function from the empty set to any set:


from-∅ : {X : Set} → ∅ → X
from-∅ ()

-- This is our first encounter of "()" patterns. They assert that a
-- case is impossible (and Agda checks that), or that no constructor
-- is available to perform a match. All uses of () can be reduced to
-- from-∅, but sometimes it is clearer to use the "()" pattern.

-- The type with one element, giving one way of representing the true
-- proposition:

data ① : Set where
 * : ① 

-- This is something like the terminal object:

to-① : {X : Set} → X → ①
to-① x = *

-- * The BHKCH intepretation of disjunction is the binary co-product,
--   inductively defined. It is natural to use the symbol "+" to
--   denote the co-product, but in Agda there is no overloading other than
--   constructors defined in (different) "data" definitions. So let's
--   use "⨄" as in the standard library


data _⨄_ (X₀ X₁ : Set) : Set where
 in₀ : X₀ → X₀ ⨄ X₁
 in₁ : X₁ → X₀ ⨄ X₁

-- These constructors correspond to the introduction rules of disjunction.
-- Definition by cases corresponds to the elimination rule:

cases : {X₀ X₁ Y : Set} → (X₀ → Y) → (X₁ → Y) → (X₀ ⨄ X₁ → Y)
cases f₀ f₁ (in₀ x₀) = f₀ x₀
cases f₀ f₁ (in₁ x₁) = f₁ x₁

-- See Bove & Dybjer's paper "Dependent types at work" for 
-- a dependently typed version of this:
-- http://www.cse.chalmers.se/~ulfn/papers/afp08/tutorial.pdf
-- Alternatively, work it out yourself as an exercise.

-- Binary co-products can be alternatively defined from sums and the
-- booleans in the presence of the "universe" Set.
--
-- First define the set of binary digits (the booleans with another
-- notation and perspective):

data ② : Set where
 ₀ : ②
 ₁ : ②

-- This amounts to if-then-else:

②-cases : {X : Set} → X → X → ② → X  
②-cases x₀ x₁ ₀ = x₀
②-cases x₀ x₁ ₁ = x₁

-- Here is the dependently-typed version:

dep-②-cases : {X : ② → Set} → X ₀ → X ₁ → ((i : ②) → X i)
dep-②-cases x₀ x₁ ₀ = x₀
dep-②-cases x₀ x₁ ₁ = x₁

-- The following has the same definition but a different type:

②-Cases : Set → Set → ② → Set  
②-Cases X₀ X₁ ₀ = X₀
②-Cases X₀ X₁ ₁ = X₁

-- Agda has universe polymorphism, but I won't mention it in this
-- tutorial. It requires to rewrite all code we have written and we
-- will write in this tutorial, everytime with a parameter for a
-- universe level. Explore the standard library to see how this works.


_⨄'_ : Set → Set → Set
X₀ ⨄' X₁ = Σ \(i : ②) → ②-Cases X₀ X₁ i

in₀' : {X₀ X₁ : Set} → X₀ → X₀ ⨄' X₁
in₀' x₀ = (₀ , x₀)

in₁' : {X₀ X₁ : Set} → X₁ → X₀ ⨄' X₁
in₁' x₁ = (₁ , x₁)

cases' : {X₀ X₁ Y : Set} → (X₀ → Y) → (X₁ → Y) → (X₀ ⨄' X₁ → Y)
cases' {X₀} {X₁} {Y} f₀ f₁ = h 
 where
  Y' : X₀ ⨄' X₁ → Set
  Y' z = Y 

  f : (i : ②) → (x : ②-Cases X₀ X₁ i) → Y'(i , x)
  f = dep-②-cases f₀ f₁

  g : (z : X₀ ⨄' X₁) → Y' z
  g = Σ-elim {②} {②-Cases X₀ X₁} {Y'} f

  h : X₀ ⨄' X₁ → Y
  h = g

-- * The BHKCH intepretation of equality:
--   
--     Howards idea: x = y is interpreted by a type that is empty if x
--     and y are equal, and has precisely one element if not. 
--
--     In set theory (classical or constructive), this can be written
--     { z ∈ 1 | x = y }, where 1 is a singleton, say {0}.
--
--     But notice that this cannot be written down in Martin-Löf's
--     type theory, and already presuposes a notion of equality to be
--     available.
-- 
--     Martin-Löf's idea: inductively define this type. This is the
--     so-called identity type, which is complicated and hence we will
--     look at it later. 


-- Using the universe Set, one can easily define equality on the
-- natural numbers by induction and show that the Martin-Löf induction
-- priciple J holds for this notion of equality on ℕ.

-- Notice that we use four stacked bars to denote the equality type on
-- the type ℕ. Later we will use three to denote the equality type, or
-- identity type, for any type (and in particular ℕ again).

infix 3 _≣_

_≣_ : ℕ → ℕ → Set
0 ≣ 0 = ① 
(succ m) ≣ 0 = ∅ 
0 ≣ (succ n) = ∅ 
(succ m) ≣ (succ n) = m ≣ n 

Reflℕ : ∀ n → n ≣ n
Reflℕ 0 = *
Reflℕ (succ n) = IH
 -- Notice that we needed to inhabit the set ((succ m) ≣ (succ n))
 -- in this case, but we instead inhabited the set (m ≣ n) using IH.
 -- This works because, by definition, ((succ m) ≣ (succ n)) is (m ≣ n).
 where
  IH : n ≣ n
  IH = Reflℕ n

-- We next show that _≣_ is the least reflexive relation on ℕ:

weak-Jℕ : (A : ℕ → ℕ → Set) → (∀ n → A n n) →  ∀ m n → m ≣ n → A m n
weak-Jℕ A φ 0 0 * = φ 0
weak-Jℕ A φ 0 (succ n) ()
weak-Jℕ A φ (succ m) 0 ()
weak-Jℕ A φ (succ m) (succ n) e = weak-Jℕ A' φ' m n e
 where
  A' : ℕ → ℕ → Set 
  A' m n = A (succ m) (succ n)
  φ' : ∀ n → A' n n
  φ' n = φ(succ n)

-- If you don't like "()" patterns, you can use the function from-∅
-- (defined above using "()" patterns):

weak-Jℕ' : (A : ℕ → ℕ → Set) → (∀ n → A n n) →  ∀ m n → m ≣ n → A m n
weak-Jℕ' A φ 0 0 * = φ 0
weak-Jℕ' A φ 0 (succ n) e = from-∅ e
weak-Jℕ' A φ (succ m) 0 e = from-∅ e
weak-Jℕ' A φ (succ m) (succ n) e = 
 weak-Jℕ' (λ m n → A(succ m)(succ n)) (λ n → φ(succ n)) m n e

-- There is a stronger, dependent(ly typed) version of weak-Jℕ:

Jℕ : (A : (m n : ℕ) → m ≣ n → Set)

   → (∀ n → A n n (Reflℕ n)) →  ∀ m n → ∀(e : m ≣ n) → A m n e

Jℕ A φ 0 0 * = φ 0
Jℕ A φ 0 (succ n) ()
Jℕ A φ (succ m) 0 ()
Jℕ A φ (succ m) (succ n) e = 
 Jℕ (λ m n → A (succ m) (succ n)) (λ n → φ(succ n)) m n e

-- Of course we could have defined instead the weak version from the
-- strong one:

weak-Jℕ'' : (A : (m n : ℕ) → Set) → (∀ n → A n n) →  ∀ m n → m ≣ n → A m n
weak-Jℕ'' A = Jℕ (λ m n e → A m n) 

-- Jℕ can be regarded as an induction principle for equality on the
-- type ℕ. Several properties of ≣ can be proved using J without
-- reference to the inductive structure of the the type ℕ, and often
-- its weak version suffices.

symℕ : (x y : ℕ) → x ≣ y → y ≣ x
symℕ = weak-Jℕ A φ 
 where
  A : (x y : ℕ) → Set
  A x y = y ≣ x
  φ : (x : ℕ) → x ≣ x
  φ = Reflℕ

transℕ : (x y z : ℕ) → x ≣ y → y ≣ z → x ≣ z
transℕ x y z r s =  transℕ' x y r z s
 where
  transℕ' : (x y : ℕ) → x ≣ y → (z : ℕ) → y ≣ z → x ≣ z
  transℕ' = weak-Jℕ A φ
   where
    A : (x y : ℕ) → Set
    A x y = ∀(z : ℕ) → y ≣ z → x ≣ z
    φ : (x : ℕ) → A x x 
    φ x z s = s

substℕ : (P : ℕ → Set) → (x y : ℕ) → x ≣ y → P x → P y
substℕ P = weak-Jℕ A φ
 where
  A : (x y : ℕ) → Set
  A x y = P x → P y
  φ : (x : ℕ) → A x x 
  φ x p = p

-- Transitivity can be proved using substitution:

sym-transℕ : (x y z : ℕ) → x ≣ y → x ≣ z → y ≣ z
sym-transℕ x y z = rearrange z x y
 where
  rearrange : (z x y : ℕ) → x ≣ y → x ≣ z → y ≣ z
  rearrange z = substℕ (λ x → x ≣ z)

transℕ' : (x y z : ℕ) → x ≣ y → y ≣ z → x ≣ z
transℕ' x y z r s = sym-transℕ y x z (symℕ x y r) s

congℕ→ℕ : (f : ℕ → ℕ) → (x x' : ℕ) → x ≣ x' → f x ≣ f x'
congℕ→ℕ f = weak-Jℕ (λ x x' → f x ≣ f x') (λ x → Reflℕ(f x)) 

-- As another example, we show that addition is commutative:

zero-is-left-neutral : ∀ n → 0 + n ≣ n 
zero-is-left-neutral 0 = *
zero-is-left-neutral (succ n) = IH  
             -- We need to inhabit the type (0 + succ n ≣ succ n). 
             -- Expanding the definitions,
             --   (0 + succ n ≣ succ n) = 
             --   (succ(0 + n) ≣ succ n) = 
             --   (0 + n ≣ n).
             -- Here "=" is definitional equality, silently applied by Agda.
 where
  IH : 0 + n ≣ n
  IH = zero-is-left-neutral n

-- Equivalently:

zero-is-left-neutral' : ∀ n → 0 + n ≣ n
zero-is-left-neutral' = induction base step
 where
  base : ①
  base = *
  step : ∀ n → 0 + n ≣ n → 0 + n ≣ n
  step n e = e

-- This with the following shows that, of course, it is equivalent to
-- define addition by induction on the first argument. The proof is by
-- induction on the second argument, following the definition of _+_.

addition-on-first : ∀ m n → (succ m) + n ≣ succ(m + n)
addition-on-first m 0 = Reflℕ m
addition-on-first m (succ n) = IH
 where
  IH : succ m + n ≣ succ(m + n)
  IH = addition-on-first m n

-- Because the situation is symmetric, we can choose any of the two
-- arguments to perform the induction in the following theorem:

addition-commutative : ∀ m n → m + n ≣ n + m
addition-commutative 0 n = zero-is-left-neutral n 
addition-commutative (succ m) n = lemma
 where
  IH : m + n ≣ n + m
  IH = addition-commutative m n
  claim : succ(m + n) ≣ succ(n + m)
  claim = congℕ→ℕ succ (m + n) (n + m) IH
  lemma : succ m + n ≣ succ (n + m)
  lemma = transℕ (succ m + n) (succ(m + n)) (succ (n + m)) 
                 (addition-on-first m n) claim


-- Exercise. Prove the Peano axioms that are not covered above. 

-- The above theorem "Jℕ" motivates Martin-Löf's inductive definition
-- of the identity type for any type X:

data _≡_ {X : Set} : X → X → Set where
 refl : {x : X} → x ≡ x

-- Martin-Löf's notation is the following:

Id : (X : Set) → X → X → Set
Id X x y  =  x ≡ y

Refl : (X : Set) → (x : X) → Id X x x
Refl X x = refl {X} {x}

-- The induction principle is as for equality on ℕ defined earlier:

J : {X : Set} → (A : (x x' : X) → x ≡ x' → Set)

   → (∀(x : X) → A x x refl) →  ∀{x x' : X} → ∀(r : x ≡ x') → A x x' r

J A f {x} refl = f x

-- In Agda, one can prove the unique-of-identity proofs principle K by
-- pattern matching:

K : {X : Set} → ∀{x x' : X} → ∀(r s : x ≡ x') → r ≡ s
K refl refl = refl

-- This is not provable in intensional Martin-Löf type theory (Hofmann
-- & Streicher's groupoid interpretation paper).
--
-- However, it is known that the following is provable in MLTT:

pseudo-K : {X : Set} → ∀{x x' : X} → ∀(r : x ≡ x') → (x , refl) ≡ (x' , r)
pseudo-K {X} = J {X} A (λ x → refl)
 where 
  A : ∀(x x' : X) → x ≡ x' → Set
  A x x' r = _≡_ {Σ \(x' : X) → x ≡ x'} (x , refl) (x' , r)

-- It has been shown that types with decidable equality, such as ℕ and
-- the booleans, satisfy the K-rule. Moreover, for ℕ it can be easily
-- proved by induction (exercise, which we may eventually do).

-- Conor McBride proved that having the K-rule is equivalent to having
-- pattern matching over refl, which Agda does. But this can be
-- disabled in Agda using the pragma {-# OPTIONS --without-K #-}.
-- Without this pragma, many definitions by pattern matching,
-- including that of J, are accepted, but that of K, and other
-- definitions that require K, are not.

-- Exercise: formulate and prove sym, subst, trans, cong, generalizing
-- the above development for ℕ. Define a weak version of J from J, and
-- use this in your proofs.

-- The propositional "axiom of function extensionality" is

Extensionality : Set₁
Extensionality = 
 ∀(X Y : Set) → ∀(f g : X → Y) → (∀(x : X) → f x ≡ g x) → f ≡ g

-- Here we have used the second universe. The first is Set = Set₀.  We
-- have Set₀ : Set₁, Set₁ : Set₂, and so on. The "small" sets (or
-- types) live in Set₀. The large set Extensionality lives in Set₁
-- because it quantifies over elements of Set₀.

-- It is neither possible to show that the set Extensionality is
-- inhabited or that it is empty. That is, the extensionality axiom is
-- independent of MLTT. We can, if we wish, postulate it, or rather
-- postulate an inhabitant:

postulate ext : Extensionality

-- But then ext behaves like a constant, with no computation rules for
-- it. Reduction gets stuck when it encounters this case.

-- The principle of excluded middle is independent of MLTT.

EM : Set₁
EM = ∀(X : Set) → X ⨄ (X → ∅)

-- Notice that (X → ∅) represents negation because ∅ represents false.
-- Notice also that the independence of EM follows from that of
-- Extensionality if we don't have the above postulate.

-- It would be good, too good, to have an inhabitant of EM without
-- violating the computational character of MLTT. It would solve
-- Hilbert's decision problem for large fragments of mathematics,
-- including Peano arithmetic. It would amount to an algorithm for
-- deciding whether a proposition has a realizer, or its negation has
-- a realizer, and would also give the corresponding realizer. As is
-- well known, this is not possible, and this is why EM cannot be
-- inhabited in MLTT.

-- This is not to say that EM is false in MLTT. 
-- In fact the set (EM → ∅) cannot be inhabited in MLTT either. This
-- is because MLTT is compatible with classical mathematics (like
-- Bishop mathematics). Set theory, say ZF with an inaccessible
-- cardinal modeling the universe, or with a stack of inaccessible
-- cardinals modelling a hierarchy of universes, can be used to give a
-- model of MLTT in which EM is inhabited (by simply using the
-- principle of excluded middle of ZF, whose consistency is not
-- disputed, even by constructive mathematicians).

-- The negation of EM is also consistent, because recursive models
-- of MLTT, in which an inhabitant of EM needs to be given by an
-- algorithm, exist, so that EM is empty and hence (EM → ∅) is
-- inhabited in such models. There are also (classical and
-- constructive) models in which all functions are continuous. In
-- those models, (EM → ∅) has an inhabitant too.

-- So it is very inaccurate to say that excluded middle "doesn't hold"
-- in Martin-Löf type theory.  What we have is that EM is independent
-- of MLTT. Independence is a meta-theoretical property, which cannot
-- be written down in MLTT itself, of course. Formalized versions of
-- the assertions "all functions are computable" and "all functions
-- are continuous" are also independent. In constructive mathematics
-- in the style of Bishop or Martin-Löf, in which compatibility with
-- classical and computational mathematics is desired, it is very easy
-- to find independent statements, as there are plenty of theorems
-- that hold classically but have no computable realizers (EM is one).

-- To be continued.

Jℕeq : (A : (m n : ℕ) → m ≣ n → Set) → (φ : (∀ n → A n n (Reflℕ n))) →  ∀ m 
     → Jℕ A φ m m (Reflℕ m) ≡ φ m
Jℕeq A φ zero = refl
Jℕeq A φ (succ m) = Jℕeq (λ m n → A (succ m) (succ n)) (λ n → φ(succ n)) m

Jℕeq17 : (A : (m n : ℕ) → m ≣ n → Set) → (φ : (∀ n → A n n (Reflℕ n)))
     → Jℕ A φ 17 17 (Reflℕ 17) ≡ φ 17
Jℕeq17 A φ = refl
