module Where where

{-
id : Set -> Set
id a = a
-}

-- x : (_ : _) -> _
x = id Set3000
  where id = \x -> x

y = False
  where data False : Set where
