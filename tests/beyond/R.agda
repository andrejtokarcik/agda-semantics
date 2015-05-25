{-

        Agda Implementors' Meeting VI

                  Göteborg
             May 24 - 3zero, 2zerozero7


                Hello Agda!

                Ulf Norell

-}

-- Records are labeled sigma types.

module R where

{-

  A very simple record.

-}

data Nat : Set where
  zero : Nat
  succ : Nat

record Point : Set where
  field x : Nat
        y : Nat

-- A record can be seen as a one constructor datatype. In this case:
data Point' : Set where
  mkPoint : (x : Nat)(y : Nat) -> Point'

-- There are a few differences, though:

-- To construct a record you use the syntax record { ..; x = e; .. }
origin : Point
origin = record { x = zero; y = zero }

-- instead of
origin' : Point'
origin' = mkPoint zero zero

-- What's more interesting is that you get projection functions
-- for free when you declare a record. More precisely, you get a module
-- parameterised over a record, containing functions corresponding to the
-- fields. In the Point example you get:
{-
  module Point (p : Point) where
    x : Nat
    y : Nat
-}

-- So Point.x : Point -> Nat is the projection function for the field x.
getX : Point -> Nat
getX = Point.x
-- getX = x
