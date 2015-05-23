\subsection{Parametrised Datatypes}

The following examples are part of a single literate \Agda file that can
be typechecked either with the official \Agda system or with \KAgda.
Each \Agda file is required to have a top-level
module -- all the program's declarations go inside it.

We introduce a new datatype straight ahead:

\begin{code}
module DepStructs where
\end{code}

\graffito{Datatypes are~written in~\acs{GADT}-style.}
%<*list>
\begin{code}
infixr 5 _::_
data List (A : Set) : Set where
  []    :                List A
  _::_  : A → List A →   List A
\end{code}
%</list>

%\vspace*{-3ex}
\AgdaSet is a universe, \ie a type whose inhabitants
can be used as types.\footnote{Obviously, if the typing relation
should not fall prey to self-referential contradictions of Russell's kind,
it must not admit \AgdaSet to be its own type -- it cannot hold
that \AgdaSet \AgdaSymbol{:}
\AgdaSet. For this reason, the universe to which \AgdaSet belongs
is of a higher level, \AgdaPrimitiveType{Set$_1$},
which in turn belongs to \AgdaPrimitiveType{Set$_2$}, and so on
\textit{ad} (countable) \textit{infinitum}. This organisation is called a predicative hierarchy of
universes. In addition, \Agda's hierarchy is non-cumulative:
it does not follow from \AgdaBound{A} \AgdaSymbol{:}
\AgdaPrimitiveType{Set$_\alpha$} that \AgdaBound{A} \AgdaSymbol{:}
\AgdaPrimitiveType{Set$_\beta$} for some \AgdaPrimitiveType{$\beta$} $\geq$
\AgdaPrimitiveType{$\alpha$}, each \AgdaBound{A} inhabits only its
particular universe.}
That constitutes the sole difference between what would
otherwise be considered value-level expressions and types,
since both values and types are expressions in \Agda: only those
expressions whose type is a universe can be themselves used as types
of other expressions.

The introduced datatype is \AgdaDatatype{List} parametrised by another
type~\AgdaBound{A}. Such a parametric declaration introduces a collection
of datatypes each of which could be in principle declared separately.

\AgdaDatatype{List} has two constructors
\AgdaInductiveConstructor{[]} (which creates a list of zero length)
and \AgdaInductiveConstructor{\_::\_} (which adds an element at the beginning of
another list; the underscores
indicate that it is an infix operator while the \AgdaKeyword{infixr}
keyword says that it is right-associative with priority \AgdaNumber{5}).
%With the minor exception of a different form of the `cons'-constructor,
%The analogy with Haskell lists should be clear.

%\todo[inline]{function composition? zip potrebuje produkt, co je record...}

Since \Agda as such comes with no base types, we have to define
some ourselves in order to provide
\AgdaDatatype{List} with an actual parameter. What about Peano-style
natural numbers?

%<*nat>
\begin{code}
data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ
\end{code}
%</nat>

Now we can create a list of natural numbers like this:

\begin{code}
[1,0,2] = one :: zero :: succ one :: []
  where one = succ zero
\end{code}

\graffito{Be scrupulous about putting spaces around
identifiers.}
The example exploits the fact that basically any continuous string of
characters counts as identifier in \Agda. The name \AgdaFunction{[1,0,2]}
that we just let denote the list-valued nullary function is as good as any
other name that would not clash with a keyword
%\footnote{The complete
%list of which can be found at Agda wiki - Lexical matters. FIXME}
or an already defined name.

\subsection{Functions} % and Implicit Arguments}
\label{sec:implargs}

The way of defining functions should be familiar to functional
programmers. A major difference is that in \Agda any pattern-matching
function (a function with at least one argument listed
in the left-hand side) must be equipped with an explicit type
signature as dependent function spaces cannot be inferred automatically
from the defining clauses~\cite{Norell2009}.
%inferred.
%, which, as we shall see, is outweighed by the power
%of dependent types.}
%Some of the similarities
%will end up to be merely superficial because with dependent types
%the same mechanisms become even more powerful.}
Functions can be introduced either by $\lambda$-terms
or clausally by left-hand-side patterns
built up from variables and data constructors.
Function applications $\beta$-reduce as usual.

If we wanted to define a function looking up an $i$-th element of a given
list at this point, we would be forced to wrap its result into
a polymorphic option type that encapsulates `meaningful' results
in addition with a `null' value.\footnote{More formally, an option type is
a tagged union of a unit type and the encapsulated type.}

The definition of the lookup function is virtually identical
to its Haskell variant, it is defined recursively with the result
wrapped within \texttt{Maybe}.
With regard to the recursive part, we recognise two cases: a base case for
where the position is \AgdaInductiveConstructor{zero} and where we return the head
of the list, and a step case where the position is
matched with \AgdaInductiveConstructor{succ} \AgdaBound{i} that
leads to a recursive call of the lookup function on structurally smaller inputs.

%<*maybe>
\begin{code}
data Maybe (A : Set) : Set where
  just     : A → Maybe A
  nothing  : Maybe A
\end{code}
%</maybe>

%<*list-lookup>
\begin{code}
infixl 4 _!!_
_!!_ : {A : Set} → List A → ℕ → Maybe A
[]          !! _         = nothing
(x  :: _)   !! zero      = just x
(_  :: xs)  !! (succ i)  = xs !! i
\end{code}
%</list-lookup>

The first argument of \AgdaFunction{\_!!\_}, being enclosed inside a pair of
curly brackets, is understood to be \emph{implicit}. The implicit function space has
the same meaning as the standard
function space (with round brackets) except that when applying the \AgdaFunction{\_!!\_} function the first argument (\ie the type parameter \AgdaBound{A} for \AgdaDatatype{List}) does not have to be explicitly supplied
and the typechecker will
attempt to figure out its value.
This effectively renders the function as (parametrically) polymorphic.

Should we need to provide a specific value for the implicit argument,
we write the function in its prefix form and provide the value in curly
brackets: 

\begin{code}
centre = _!!_ {ℕ} [1,0,2] zero
\end{code}

To imitate the default automatic behaviour we could put a \emph{metavariable}
in place of the term that \Agda should infer on its own:

\begin{code}
centre' = _!!_ {_} [1,0,2] zero
\end{code}

The underscore represents a non-interactive, `go figure'
metavariable (as opposed to the other kinds of metavariables
%and interaction points
used during interactive development that we do not discuss here).
Also note that an underscore occurring in the left-hand side
works as a wildcard pattern or an anonymous variable that matches
any input, not as an actual metavariable.

The disadvantage of \AgdaFunction{\_!!\_} is that its user
is always left with the burden of manual extraction of the actual result
even when an empty list is certain to be never passed in.
Such annoyances are unavoidable with lists because they do not contain
the structure's length as part of their type information. Put simply,
any function that accepts a \AgdaDatatype{List}
must cover all possible lengths of the input.

\subsection{Inductive Families}

With dependent types we can internalise
the length information as an \emph{index} of the datatype that consequently
allows for the function's type to be more articulate and to exclude, say,
empty structures. The \AgdaDatatype{Maybe} workaround is not needed anymore
because the type itself demands that
the function gets applied to non-empty structures exclusively.

%<*vec>
\begin{code}
infixr 5 _,_
data Vec (A : Set) : ℕ → Set where
  <>   :                          Vec A  zero
  _,_  : {n : ℕ} → A → Vec A n →  Vec A (succ n)
\end{code}
%</vec>

The declaration introduces an inductively defined \emph{family} of datatypes
indexed by the length.
In addition to being parametrised like \AgdaDatatype{List} (parameters are
to the left of the colon in the type declaration),
a vector is also indexed by a natural number (to the right of the colon) that encodes
the length of the particular data structure.

For instance, one member of this family is the type
\AgdaDatatype{Vec} \AgdaDatatype{ℕ} \AgdaSymbol{(}\AgdaInductiveConstructor{succ}
\AgdaInductiveConstructor{zero}\AgdaSymbol{)}.
The expression \AgdaInductiveConstructor{zero}
\AgdaInductiveConstructor{,} \AgdaInductiveConstructor{<>}
has this type. On the contrary, neither \AgdaInductiveConstructor{<>} (its
index is zero, not one) nor
\AgdaSymbol{(}\AgdaInductiveConstructor{just}
\AgdaInductiveConstructor{zero}\AgdaSymbol{)}
\AgdaInductiveConstructor{,} \AgdaInductiveConstructor{<>} (it is parametrised
by \AgdaDatatype{Maybe} \AgdaDatatype{ℕ} instead of plain \AgdaDatatype{ℕ})
are expressions of that type.

The parameter differs from the vector in that the 
former is invariant and fixed %across the scope of the whole definition
while the latter
varies and is defined locally per constructor so that
all possible values for the index are targeted.
%\footnote{It should be noted that this manner of distinguishing between parameters and indices is rather idiosyncratic
%and limited to the circle of \Agda users.
%Especially, there are semantic differences between the `traditional'
%terminology as given by \citet{Dybjer1997} and the nomenclature employed here.}
%The target of all data constructors is the type \AgdaDatatype{Vec} \AgdaBound{A}
%\AgdaBound{n} for some \AgdaBound{n} \AgdaSymbol{:} \AgdaDatatype{ℕ} that
%may vary for each constructor whereas \AgdaBound{A} remains
%the same.
It is not possible anymore to define each member of the inductive family
independently of others as it was with collections of parametrised datatypes.

Now we may proceed to the definition of the lookup function for vectors
whose safety is guaranteed by the type checker. First,
we call the datatype of finite sets to our aid:

%<*fin>
\begin{code}
data Fin : ℕ → Set where
  fzero : {n : ℕ} → Fin (succ n)
  fsucc : {n : ℕ} → Fin n →  Fin (succ n)
\end{code}
%</fin>

\AgdaDatatype{Fin} \AgdaBound{n} contains exactly \AgdaBound{n}
elements. The idea is that the lookup function accepts only elements of
a finite set $\{0, 1, \dots, n - 1\}$ as positions to be looked up
in a vector of length $n$:

%<*vec-lookup>
\begin{code}
infixl 4 _[_]
_[_]  : {A : Set} {n : ℕ} → Vec A n → Fin n → A
<>         [ () ]
(x  ,  _)  [ fzero ]    = x
(_  , xs)  [ fsucc i ]  = xs [ i ]
\end{code}
%</vec-lookup>

The first clause has the \emph{absurd pattern} `\AgdaSymbol{()}'
to signify that the case is to be rejected by the type
checker because no
suitable constructors can be used (in this case,
there are no constructors for  \AgdaDatatype{Fin} \AgdaInductiveConstructor{zero}).
Naturally, no right-hand side needs to be provided in such a case.
A well-typed application of \AgdaFunction{\_[\_]} is thus guaranteed
to involve a~non-empty vector and to evaluate to an element\footnote{The
type per se does not capture the fact
that the result is the vector's $i$-th element -- a function
that ignores the position and always returns the first element
is a term of that type, too.}
of the vector.

\subsection{Inaccessible Patterns}

In the last function definition, the vector indicies were all
conveniently implicit.
%It is important to know what goes under the hood, though.
%To the first approximation, we consider the following code with all
%the arguments made explicit:
%
%\begin{code}
%{-
%-- _[_]'  : {A : Set} {n : ℕ} → Vec A n → Fin n → A
%-- _[_]' {A}  {zero}    <>              ()
%-- _[_]' {A}  {succ n}  (_,_ {n} x _)   fzero      = x
%-- _[_]' {A}  {succ n}  (_,_ {n} _ xs)  (fsucc i)  =
%--                                          _[_]' {A} {n} xs i
%-}
%\end{code}
%%\begin{code}
%%{-
%%  _[_]'  : {A : Set} {n : ℕ} → Vec A n → Fin n → A
%%  _[_]' {A}  {zero}     <>              ()
%%  _[_]' {A}  {succ n}   (_,_ {n} x _)   fzero      = x
%%  _[_]' {A}  {succ n}   (_,_ {n} _ xs)  (fsucc i)  = _[_]' {A} {n} xs i
%%-}
%%\end{code}
%The code is commented out because the typechecker otherwise complains
If we tried to make it implicit, we would soon find out that the typechecker
complains about a variable occurring multiple times in a~left-hand
side. \Agda requires patterns to be \emph{linear}, that is, the same
variable must not occur more than once. This is not a big deal
in languages without dependent types that can consider each of the arguments
independently. Here, however, 
the issue of pattern non-linearity necessarily arises
due to mutually related datatype indices.
We lose the ability
to match each argument separately %and have to consider
%the left-hand side as a whole
since pattern-matching on one argument can enforce
the value of other arguments by instantiation of datatype indices.

This is when \emph{inaccessible patterns}, prefixed with a dot,
come into play:

\begin{code}
_[_]'  : {A : Set} {n : ℕ} → Vec A n → Fin n → A
_[_]' {A}  {zero}     <>              ()
_[_]' {A}  {succ .n}  (_,_ {n} x _)   fzero      = x
_[_]' {A}  {succ .n}  (_,_ {n} _ xs)  (fsucc i)  =
                                            _[_]' {A} {n} xs i
\end{code}

The accessible portion of the left-hand side must form a linear pattern.
%with its individual parts being either variables or constructor
%applications. 
The inaccessible parts are used only for typechecking; they are discarded
at run time during actual pattern matching
as they are certain to match once they have typechecked~\cite{Bove2009}.
