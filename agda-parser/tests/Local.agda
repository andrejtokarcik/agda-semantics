-- from http://wiki.portal.chalmers.se/agda/pmwiki.php?n=ReferenceManual.LocalDefinition

module Local where

  data Nat : Set where
    zero : Nat
    succ : Nat -> Nat  

  infixl 5 _+_
  _+_ : Nat -> Nat -> Nat
  zero + n = n
  (succ m) + n = succ (m + n)

  infixl 6 _*_
  _*_ : Nat -> Nat -> Nat
  zero * _ = zero
  (succ m) * n = n + m * n

  f : Nat
  f =  let h : Nat -> Nat
           h m = succ (succ m)
        in h zero + h (succ zero)

  h : Nat -> Nat
  h n = let add2 : Nat
            add2 = succ (succ n)

            twice : Nat -> Nat
            twice m = m * m

        in twice add2

  g : Nat -> Nat
  g n = fib n + fact n
   where fib : Nat -> Nat
         fib zero = succ zero
         fib (succ zero) = succ zero
         fib (succ (succ n)) = fib (succ n) + fib n

         fact : Nat -> Nat
         fact zero = succ zero
         fact (succ n) = succ n * fact n

  k : Nat -> Nat
  k n = let aux : Nat -> Nat
            aux m = pred (g m) + h m
        in aux (pred n)
    where pred : Nat -> Nat
          pred zero = zero
          pred (succ m) = m
