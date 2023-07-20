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

from n (threeGenCommutativityLeft r p q i j)  = threeGenCommutativityComposition r p q i j
from n (threeGenCommutativityMiddle r p q i j) = hcomp (λ {  k ( i = i0)    →  gen r p j
                                                           ; k ( i = i1)    →  genEquality q p k (~ j)
                                                           ; k ( j = i0)    →  threeGenCommutativity r p q (~ k) i
                                                           ; k ( j = i1)    →  genEquality q r k i 
                                                           }) (threeGenCommutativityComposition q r p i j)


                                                                            -- r p q = (A p q) (A r p) (A r q)
                                                                            -- q r p = (A r p) (A q r) (A q p)
                                                                            -- p q r = (A q r) (A p q) (A p r)

--                                                                A r q
--                                                       b - - - - - - - - > b
--                                            A r p   /  ^                 / ^     
--                                                  /    |      sym Apq  /   |
--                                                /      |             /     |
--                                               b - - - - - - - - > b       |
--                                               ^      conn r p q   ^       |                    ^  j
--                                               |       |           |       |                  k | /
--                                               |       |           |       |                    ∙ — >
--                                               |       |   A q r   |       |                      i
--                                               |       b - - - - - | - - > b
--                                               |     /             |     /
--                                               |   / Arp           |   /   sym (A q p)
--                                               | /                 | /
--                                               b - - - - - - - - > b
--                                                     conn q r p  



from n (threeGenCommutativityRight r p q i j) = hcomp (λ {   k ( i = i0)    → genEquality q r k j
                                                           ; k ( i = i1)    → genEquality p r k (~ j)
                                                           ; k ( j = i0)    → ((threeGenCommutativity r p q) ∙ (threeGenCommutativity q r p)) (~ k) i
                                                           ; k ( j = i1)    → gen p q i
                                                           }) (threeGenCommutativityComposition p q r i j)


--                                                                Apq
--                                                       b - - - - - - - - > b
--                                            A r q   /  ^                 / ^     
--                                                  /    |      sym Arp  /   |
--                                                /      |             /     |
--                                               b - - - - - - - - > b       |
--                                               ^      conn r p q   ^       |                    ^  j
--                                               |       |           |       |                  k | /
--                                               |       |           |       |                    ∙ — >
--                                               |       |   Apq     |       |                      i
--                                               |       b - - - - - | - - > b
--                                               |     /             |     /
--                                               |   / Aqr           |   /   sym Apr
--                                               | /                 | /
--                                               b - - - - - - - - > b
--                                                     conn p q r 






from n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) = fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i
from n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) = fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j
from n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) = fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j






PBraid-Iso-PBraid' : ∀ n →  Iso (BPureBraid n) (BPureBraid' n)
PBraid-Iso-PBraid' n = iso (to n) (from n) sec ret
    where 
        sec : section (to n) (from n)
        sec base = refl
        sec (gen p q i) j = gen p q i
        sec (identity p i j) k = identity p i j
        sec (genEquality p q i j) k = genEquality p q i j
        sec (twoGenCommutativity1 p q r s proof-rp proof-sp proof-rq proof-sq i j) k = twoGenCommutativity1 p q r s proof-rp proof-sp proof-rq proof-sq i j
        sec (twoGenCommutativity2 p q r s proof-pr proof-ps proof-rq proof-sq i j) k = twoGenCommutativity2 p q r s proof-pr proof-ps proof-rq proof-sq i j
        sec (threeGenCommutativityConnector r p q i) j = threeGenCommutativityConnector r p q i



        sec (threeGenCommutativityLeft r p q i j) k = {!   !} --compPathP-filler {!   !} {!   !} {!   !} {!   !}

        --                                                      Arp
--                                                       b - - - - - - - - > b
--                                            A p q   /  ^                 / ^     
--                                                  /    |      sym Arq  /   |
--                                                /      |             /     |
--                                               b - - - - - - - - > b       |
--                                               ^      conn r p q   ^       |                    ^  j
--                                               |       |           |       |                  k | /
--                                               |       |           |       |                    ∙ — >
--                                               |       |   Arp     |       |                      i
--                                               |       b - - - - - | - - > b
--                                               |     /             |     /
--                                               |   / Apq           |   /   sym Arq
--                                               | /                 | /
--                                               b - - - - - - - - > b
--                                                     conn r p q 
        
        sec (threeGenCommutativityMiddle r p q i j) k = {!   !}
        sec (threeGenCommutativityRight r p q i j) k = {!   !}
        sec (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) j = fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i
        sec (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) k = fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j
        sec (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) k = fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j

        ret : retract (to n) (from n)
        ret base = refl
        ret (gen p q i) j = gen p q i
        ret (identity p i j) k = identity p i j
        ret (genEquality p q i j) k = genEquality p q i j
        ret (twoGenCommutativity1 p q r s proof-rp proof-sp proof-rq proof-sq i j) k = twoGenCommutativity1 p q r s proof-rp proof-sp proof-rq proof-sq i j
        ret (twoGenCommutativity2 p q r s proof-pr proof-ps proof-rq proof-sq i j) k = twoGenCommutativity2 p q r s proof-pr proof-ps proof-rq proof-sq i j
        ret (threeGenCommutativityConnector r p q i) j = threeGenCommutativityConnector r p q i
        ret (threeGenCommutativityComposition r p q i j) k = {!   !}
        ret (threeGenCommutativity r p q i j) k  = {! thre  !}
        ret (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) j = fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i
        ret (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) k = fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j
        ret (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) k = fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j

  
        