module exampleTypeAbbreviations where

postulate A : Set
A2 : Set
A2 = A -> A

A3 : Set
A3 = A2 -> A2

a2 : A2
a2 = \x -> x

a3 : A3
a3 = \x -> x