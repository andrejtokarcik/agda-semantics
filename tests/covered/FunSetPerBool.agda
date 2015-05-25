module FunSetPerBool where

data Bool : Set where
  True : Bool
  False : Bool

data T : Set where
  E : T

s : Bool -> Set
s True = Bool
s False = T

f = \ (x : s True) -> x
g = f True
f2 = \ (x : Bool) (y : s x) -> y
h = f2 False E
-- i : (xx : _) -> _
i = f2 True
j : (eh : s False) -> s False
j = f2 False
