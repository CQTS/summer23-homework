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


from n (threeGenCommutativityConnector r p q i) = threeGenCommutativityConnector r p q i
-- with fst p ≟ fst q   | fst r ≟ fst p | fst r ≟ fst q
-- ...                                                 | (lt proof)     | (lt proof2)| (lt proof3) = threeGenCommutativityConnector r p q proof2 proof i
-- ...                                                 | (gt proof)     | (gt proof2)| (gt proof3) = threeGenCommutativityConnector q p r proof proof2 i
-- ...                                                 | _              | _          | _           = base 



from n (threeGenCommutativityLeft r p q i j) with fst p ≟ fst q   | fst r ≟ fst p | fst r ≟ fst q
...                                                 | (lt proof)     | (lt proof2)| (lt proof3) = threeGenCommutativityLeft r p q proof2 proof i j
...                                                 | (gt proof)     | (gt proof2)| (gt proof3) = {!   !} -- threeGenCommutativityLeft q p r proof proof2 {!   !} {!   !} 
-- hcomp  (λ { k ( i = i0)    →   {!   !} -- (genEquality q p) ? ?  -- questionable
                                                                                                            -- ; k ( i = i1)    →   genEquality q r k (~ j)
                                                                                                            -- ; k ( j = i0)    → threeGenCommutativityConnector q p r  i
                                                                                                            -- ; k ( j = i1)    →  (genEquality p r) k {! i  !} }) -- questionable
                                                                                                            -- (threeGenCommutativityLeft q p r proof proof2 i j)

...                                                 | (lt proof)     | (lt proof2)| (eq proof3) = {! ⊥.rec   !}
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




from n (threeGenCommutativityMiddle r p q i j) = {!   !}
from n (threeGenCommutativityRight r p q i j) = {!   !}




from n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) = fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i
from n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) = fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j
from n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) = fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j






PBraid-Iso-PBraid' : ∀ n →  Iso (BPureBraid n) (BPureBraid' n)
PBraid-Iso-PBraid' n = iso (to n) (from n) sec ret
    where 
        sec : section (to n) (from n)
        sec base = refl
        sec (gen p q i) j = (gen p q) i
        sec (identity p i j) k = identity p i j
        sec (genEquality p q i j) k = genEquality p q i j
        sec (twoGenCommutativity1 p q r s proof-rp proof-sp proof-rq proof-sq i j) k = twoGenCommutativity1 p q r s proof-rp proof-sp proof-rq proof-sq i j
        sec (twoGenCommutativity2 p q r s proof-pr proof-ps proof-rq proof-sq i j) k = twoGenCommutativity2 p q r s proof-pr proof-ps proof-rq proof-sq i j
        sec (threeGenCommutativityConnector r p q i) j = {!   !}
        sec (threeGenCommutativityLeft r p q i j) k = {!   !}
        sec (threeGenCommutativityMiddle r p q i j) k = {!   !}
        sec (threeGenCommutativityRight r p q i j) k = {!   !}
        sec (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) j = fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i
        sec (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) k = fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j
        sec (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) k = fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j

        ret : retract (to n) (from n)
        ret base = {!   !}
        ret (gen p q i) = {!   !}
        ret (identity p i j) = {!   !}
        ret (genEquality p q i j) = {!   !}
        ret (twoGenCommutativity1 p q r s proof-rp proof-sp proof-rq proof-sq i j) = {!   !}
        ret (twoGenCommutativity2 p q r s proof-pr proof-ps proof-rq proof-sq i j) = {!   !}
        ret (threeGenCommutativityConnector r p q i) = {!   !}
        ret (threeGenCommutativityLeft r p q proof-rp proof-pq i j) = {!   !}
        ret (threeGenCommutativityMiddle r p q proof-rp proof-pq i j) = {!   !}
        ret (threeGenCommutativityRight r p q proof-rp proof-pq i j) = {!   !}
        ret (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) = {!   !}
        ret (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) = {!   !}
        ret (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) = {!   !}

  
     