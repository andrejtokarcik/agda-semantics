To make it more clear, let us prove a simple theorem in \Agda.
We will show that zero is a right identity element with respect to
addition of natural numbers.

\begin{comment}
\begin{code}
module CurryHoward where
\end{code}
\end{comment}

\begin{comment}
\begin{code}
data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ
\end{code}
\end{comment}

First, we define the addition itself by primitive recursion in the first argument:

\begin{code}
infixl 6 _+_
_+_ : ℕ → ℕ → ℕ
zero      + m  = m
(succ n)  + m  = succ (n + m)
\end{code}

Further we need a means to reason about equality within \Agda types
because we cannot directly prove any properties of
\Agda's built-in definitional equality:\footnote{The internal notion of
equality views those terms as equal that normalise to the same
value~\cite{Abel2012}. Normalisation involves $\beta$-reduction and rewriting
according to function clauses (by pattern matching). Fast-forward
to \autoref{sec:nf} for more technical details.}
%We discuss issues regarding equality in more detail in \autoref{sec:equality}.

\begin{code}
infix 4 _≡_
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x
\end{code}

\AgdaDatatype{\_≡\_} is the diagonal relation on \AgdaBound{A}.
In set theory, it would be defined as the least binary relation
on a set $A$ such that $x \equiv x$ for all $x \in A$.
In type-theoretic terms it is a family of proofs of ``being \emph{propositionally} equal
to \AgdaBound{x}'' that is inhabited only when the index is \emph{definitionally}
equal to \AgdaBound{x}; \AgdaInductiveConstructor{refl} is the %(sole)
witness that the two terms of type \AgdaBound{A} are equal.
We have thus exposed the internal notion of equality
so that it is amenable to be a component of types/propositions.

The equality relation is also a congruence in the sense that it is compatible
with unary functions:

\begin{code}
cong : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong _ refl = refl
\end{code}

Beware that \AgdaInductiveConstructor{refl}
in the left-hand side is not identical to the constructor of the same name
in the right-hand side. What we match on is the witness that \AgdaBound{x}
and \AgdaBound{y} are equal, whereas \AgdaInductiveConstructor{refl} to the right
is the witness of \AgdaBound{f} \AgdaBound{x} \AgdaDatatype{≡} \AgdaBound{f} \AgdaBound{y}. This constellation is certain to typecheck thanks to
the fact that \AgdaBound{x} \AgdaDatatype{≡} \AgdaBound{y} (which is proven
by the input witness) and the
fact that \AgdaBound{f} is a function (any function
%by definition
gives the same value whenever it is applied to the same/equal argument).

Now that we have everything prepared we can come to grips with the desired theorem:

\graffito{The type can\\ be read as $\forall n \in \mathbb{N}\,.\,n + 0 \equiv n$.}
\begin{code}
thm : (n : ℕ) → n + zero ≡ n
thm  zero     = refl
thm (succ n)  = cong succ (thm n)
\end{code}

The proof is by induction on \AgdaBound{n}. The base case is most simple:
\AgdaInductiveConstructor{zero} \AgdaFunction{+} \AgdaInductiveConstructor{zero}
reduces to \AgdaInductiveConstructor{zero} and so all we need to prove is
that \AgdaInductiveConstructor{zero} \AgdaDatatype{≡} \AgdaInductiveConstructor{zero}.

In the step case, we get \AgdaInductiveConstructor{succ} \AgdaSymbol{(}\AgdaBound{n} \AgdaFunction{+} \AgdaInductiveConstructor{zero}\AgdaSymbol{)}
after reduction per the second clause of \AgdaFunction{\_+\_}.
We then rely on the hypothesis that the theorem holds
for the structurally smaller number, namely \AgdaBound{n},
to build up a proof of \AgdaInductiveConstructor{succ} \AgdaSymbol{(}\AgdaBound{n} \AgdaFunction{+} \AgdaInductiveConstructor{zero}\AgdaSymbol{)}
\AgdaDatatype{≡} \AgdaInductiveConstructor{succ} \AgdaBound{n} using
the congruence property.


Note that the theorem does not take advantage of the way
in which addition is defined.
On the other hand, if the theorem was formulated with
\AgdaInductiveConstructor{zero} \AgdaFunction{+} \AgdaBound{n} \AgdaDatatype{≡} \AgdaBound{n},
the function application would immediately get reduced
in accordance with the first clause of \AgdaFunction{\_+\_}.
The proof thereof would be trivial, too:

\begin{code}
thmEasy : (n : ℕ) → zero + n ≡ n
thmEasy _     = refl
\end{code}

Both theorems show that \Agda can and does normalise
\emph{open} expressions (containing free variables) during typechecking.
In non-dependent functional languages, this kind of normalisation is
performed only during proper execution of the program (their types do not
involve usual function applications) and even then
only to simplify \emph{closed} expressions~\cite[sec.~5.2]{Bove2009}.

All in all, programming really ends up to be proving.
