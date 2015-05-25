module maryjohn2 where


postulate Person        : Set
postulate john          : Person
postulate mary          : Person
postulate barbara       : Person
postulate IsStudent     : Person -> Set
postulate maryIsStudent : IsStudent mary
postulate implication   : IsStudent mary -> IsStudent john

Lemma1 : Set
Lemma1 = IsStudent john


proof-lemma1 : Lemma1
proof-lemma1 = implication maryIsStudent

Lemma2 : Set
Lemma2 = IsStudent john -> IsStudent barbara

proof-lemma2 : Lemma2
proof-lemma2 = \(x : IsStudent john) -> _
