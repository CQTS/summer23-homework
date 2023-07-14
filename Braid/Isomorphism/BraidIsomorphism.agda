{-# OPTIONS --safe #-}
module Braid.Isomorphism.BraidIsomorphism where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat.Base
open import Cubical.Data.Fin.Base
open import Cubical.Data.Empty as ⊥
open import Cubical.Foundations.Isomorphism 
open import Cubical.Data.Nat.Order renaming (pred-≤-pred to pred)

open import Braid.PureBraidAlt
open import Braid.PureBraid










BPureBraid'→BPureBraid : ∀ n → (b : BPureBraid' n) → BPureBraid n 
BPureBraid'→BPureBraid n base = base
BPureBraid'→BPureBraid n (gen p q constraint i) = gen p q i
BPureBraid'→BPureBraid n (commutativity1 p q r s proof-rs proof-sp proof-pq i j) = twoGenCommutativity1 p q r s (<-trans proof-rs proof-sp) proof-sp (<-trans (<-trans proof-rs proof-sp) proof-pq) (<-trans proof-sp proof-pq) i j
BPureBraid'→BPureBraid n (commutativity2 p q r s proof-pr proof-rs proof-sq proof-pq i j) = twoGenCommutativity2 p q r s proof-pr (<-trans proof-pr proof-rs) (<-trans proof-rs proof-sq) proof-sq i j
BPureBraid'→BPureBraid n (threewayCommutativityCommon r p q proof-rp proof-pq proof-rq i) = threeGenCommutativityConnector r p q proof-rp proof-pq i
BPureBraid'→BPureBraid n (threewayCommutativityLeft r p q proof-rp proof-pq proof-rq i j) = threeGenCommutativityLeft r p q proof-rp proof-pq i j
BPureBraid'→BPureBraid n (threewayCommutativityRight r p q proof-rp proof-pq proof-rq i j) = threeGenCommutativityMiddle r p q proof-rp proof-pq i j
BPureBraid'→BPureBraid n (threewayCommutativityTop r p q proof-rp proof-pq proof-rq i j) = threeGenCommutativityRight r p q proof-rp proof-pq i j
BPureBraid'→BPureBraid n (fourwayCommutativityConnector r p s q proof-rp proof-ps proof-sq proof-rq proof-pq i) = fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i
BPureBraid'→BPureBraid n (fourwayCommutativityComposition r p s q proof-rp proof-ps proof-sq proof-rq proof-pq i j) = fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j
BPureBraid'→BPureBraid n (fourwayCommutativity r p s q proof-rp proof-ps proof-sq proof-rs proof-rq proof-pq i j) = fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j 






Iso-PBraid-PBraid' : ∀ n →  Iso (BPureBraid n) (BPureBraid' n)
Iso-PBraid-PBraid' n = iso ({!   !} n) (BPureBraid'→BPureBraid n) s r
    where
        s : section ({!   !} n) (BPureBraid'→BPureBraid n)
        s = {!   !}

        r : retract ({!   !} n) (BPureBraid'→BPureBraid n)
        r = {!   !}

  
