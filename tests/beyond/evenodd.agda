module evenodd where

mutual
  data Even : Set where
    Z  : Even
    S  : Odd -> Even

  data Odd : Set where
    S' : Even -> Odd 
  
