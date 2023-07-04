{-# OPTIONS --safe #-}


module homework.braid.PureBraidGroup where
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat.Base
open import Cubical.Data.Fin.Base



data B3 : Type where
  base  : B3
  generator1 : base ≡ base
  generator2 : base ≡ base
  relation : Square generator1 generator1 generator2 generator2
  makeGroupoid : {x y : B3} → isSet (x ≡ y)
  


-- data BPureBraid : (n : ℕ) → Type where -- the space whose loops are the pure braid group


    
 


 