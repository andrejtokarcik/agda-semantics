
-- This module introduces implicit arguments.

module Id8 where

id8 : {A : Set} -> A -> A
id8 = \{A} x -> x        -- this doesn't work since the type checker assumes
                            -- that the implicit A has been has been omitted in
                            -- the left-hand side (as in id6).
