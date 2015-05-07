-- AT: should not pass with orig agda according to some sources (agda wiki?)
--     but is okay in actuality

module Berry where
data Bool : Set where
  tt : Bool
  ff : Bool

-- Berry's majority function
maj : Bool -> Bool -> Bool -> Bool
maj tt tt tt = tt
maj tt ff x  = x
maj ff x  tt = x
maj x  tt ff = x
maj ff ff ff = ff
