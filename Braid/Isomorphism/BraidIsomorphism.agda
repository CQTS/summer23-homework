{-# OPTIONS --safe #-}
module Braid.Isomorphism.BraidIsomorphism where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat.Base
open import Cubical.Data.Fin.Base
open import Cubical.Data.Empty as ⊥
open import Cubical.Foundations.Isomorphism 
open import Cubical.Data.Nat.Order renaming (pred-≤-pred to pred)

open import Braid.PureBraidReducedConstraints
open import Braid.PureBraid
open import Braid.Isomorphism.function renaming (BPureBraid→BPureBraid' to to)





from : ∀ n → (b : BPureBraid' n) → BPureBraid n 
from n base = base
from n (gen p q i) = gen p q i
from n (identity p i j) = identity p i j
from n (genEquality p q i j) = genEquality p q i j
from n (twoGenCommutativity1 p q r s proof-rp proof-sp proof-rq proof-sq i j) = twoGenCommutativity1 p q r s proof-rp proof-sp proof-rq proof-sq i j
from n (twoGenCommutativity2 p q r s proof-pr proof-ps proof-rq proof-sq i j) = twoGenCommutativity2 p q r s proof-pr proof-ps proof-rq proof-sq i j


from n (threeGenCommutativityConnector r p q i) with fst p ≟ fst q   | fst r ≟ fst p | fst r ≟ fst q
...                                                 | (lt proof)     | (lt proof2)| (lt proof3) = threeGenCommutativityConnector r p q proof2 proof i
...                                                 | (lt proof)     | (lt proof2)| (eq proof3) = base
...                                                 | (lt proof)     | (lt proof2)| (gt proof3) = base

...                                                 | (lt proof)     | (eq proof2)| (lt proof3) = base
...                                                 | (lt proof)     | (eq proof2)| (eq proof3) = base
...                                                 | (lt proof)     | (eq proof2)| (gt proof3) = base

...                                                 | (lt proof)     | (gt proof2)| (lt proof3) = base
...                                                 | (lt proof)     | (gt proof2)| (eq proof3) = base
...                                                 | (lt proof)     | (gt proof2)| (gt proof3) = base

...                                                 | (eq proof)     | (lt proof2)| (lt proof3) = base
...                                                 | (eq proof)     | (lt proof2)| (eq proof3) = base
...                                                 | (eq proof)     | (lt proof2)| (gt proof3) = base

...                                                 | (eq proof)     | (eq proof2)| (lt proof3) = base
...                                                 | (eq proof)     | (eq proof2)| (eq proof3) = base
...                                                 | (eq proof)     | (eq proof2)| (gt proof3) = base

...                                                 | (eq proof)     | (gt proof2)| (lt proof3) = base
...                                                 | (eq proof)     | (gt proof2)| (eq proof3) = base
...                                                 | (eq proof)     | (gt proof2)| (gt proof3) = base

...                                                 | (gt proof)     | (lt proof2)| (lt proof3) = base
...                                                 | (gt proof)     | (lt proof2)| (eq proof3) = base
...                                                 | (gt proof)     | (lt proof2)| (gt proof3) = base

...                                                 | (gt proof)     | (eq proof2)| (lt proof3) = base
...                                                 | (gt proof)     | (eq proof2)| (eq proof3) = base
...                                                 | (gt proof)     | (eq proof2)| (gt proof3) = base

...                                                 | (gt proof)     | (gt proof2)| (lt proof3) = base
...                                                 | (gt proof)     | (gt proof2)| (eq proof3) = base
...                                                 | (gt proof)     | (gt proof2)| (gt proof3) = threeGenCommutativityConnector q p r proof proof2 i


from n (threeGenCommutativityLeft r p q i j) with fst p ≟ fst q   | fst r ≟ fst p | fst r ≟ fst q
...                                                 | (lt proof)     | (lt proof2)| (lt proof3) = threeGenCommutativityLeft r p q proof2 proof i j
...                                                 | (lt proof)     | (lt proof2)| (eq proof3) = {!   !}
...                                                 | (lt proof)     | (lt proof2)| (gt proof3) = {!   !}

...                                                 | (lt proof)     | (eq proof2)| (lt proof3) = {!   !}
...                                                 | (lt proof)     | (eq proof2)| (eq proof3) = {!   !}
...                                                 | (lt proof)     | (eq proof2)| (gt proof3) = {!   !}

...                                                 | (lt proof)     | (gt proof2)| (lt proof3) = {!   !}
...                                                 | (lt proof)     | (gt proof2)| (eq proof3) = {!   !}
...                                                 | (lt proof)     | (gt proof2)| (gt proof3) = {!   !}

...                                                 | (eq proof)     | (lt proof2)| (lt proof3) = {!   !}
...                                                 | (eq proof)     | (lt proof2)| (eq proof3) = {!   !}
...                                                 | (eq proof)     | (lt proof2)| (gt proof3) = {!   !}

...                                                 | (eq proof)     | (eq proof2)| (lt proof3) = {!   !}
...                                                 | (eq proof)     | (eq proof2)| (eq proof3) = {!   !}
...                                                 | (eq proof)     | (eq proof2)| (gt proof3) = {!   !}

...                                                 | (eq proof)     | (gt proof2)| (lt proof3) = {!   !}
...                                                 | (eq proof)     | (gt proof2)| (eq proof3) = {!   !}
...                                                 | (eq proof)     | (gt proof2)| (gt proof3) = {!   !}

...                                                 | (gt proof)     | (lt proof2)| (lt proof3) = {!   !}
...                                                 | (gt proof)     | (lt proof2)| (eq proof3) = {!   !}
...                                                 | (gt proof)     | (lt proof2)| (gt proof3) = {!   !}

...                                                 | (gt proof)     | (eq proof2)| (lt proof3) = {!   !}
...                                                 | (gt proof)     | (eq proof2)| (eq proof3) = {!   !}
...                                                 | (gt proof)     | (eq proof2)| (gt proof3) = {!   !}

...                                                 | (gt proof)     | (gt proof2)| (lt proof3) = {!   !}
...                                                 | (gt proof)     | (gt proof2)| (eq proof3) = {!   !}
...                                                 | (gt proof)     | (gt proof2)| (gt proof3) = doubleCompPath-filler (gen q p) (sym (gen q r)) (gen p r) {!  i !}  {!   !} --threeGenCommutativityLeft q p r proof proof2 {! i !} {!   !}




from n (threeGenCommutativityMiddle r p q i j) = {!   !}
from n (threeGenCommutativityRight r p q i j) = {!   !}




from n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) = fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i
from n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) = fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j
from n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) = fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j






PBraid-Iso-PBraid' : ∀ n →  Iso (BPureBraid n) (BPureBraid' n)
PBraid-Iso-PBraid' n = iso (to n) (from n) s r
    where 
        s : section (to n) (from n)
        s base = {!   !}
        s (gen p q i) = {!   !}
        s (identity p i j) = {!   !}
        s (genEquality p q i j) = {!   !}
        s (twoGenCommutativity1 p q r s₁ proof-rp proof-sp proof-rq proof-sq i j) = {!   !}
        s (twoGenCommutativity2 p q r s₁ proof-pr proof-ps proof-rq proof-sq i j) = {!   !}
        s (threeGenCommutativityConnector r p q i) = {!   !}
        s (threeGenCommutativityLeft r p q i j) = {!   !}
        s (threeGenCommutativityMiddle r p q i j) = {!   !}
        s (threeGenCommutativityRight r p q i j) = {!   !}
        s (fourGenCommutativityConnector r p s₁ q proof-rp proof-ps proof-sq i) = {!   !}
        s (fourGenCommutativityComposition r p s₁ q proof-rp proof-ps proof-sq i j) = {!   !}
        s (fourGenCommutativity r p s₁ q proof-rp proof-ps proof-sq i j) = {!   !}

        r : retract (to n) (from n)
        r b  = {!   !}

  
  