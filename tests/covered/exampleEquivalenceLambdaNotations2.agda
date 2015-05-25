module exampleEquivalenceLambdaNotations2 where


postulate A : Set

g : A -> A
g = \x -> x

g' : A -> A
g' a = a

postulate P : (A -> A) -> Set

f : P g -> P g'
f x = x
