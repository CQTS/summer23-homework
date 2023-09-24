{-
Incorrect implementation of map
-}



{-# OPTIONS --safe #-}

module Braid.Subgroup.PureBraidtoBraid where

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude 
open import Cubical.Data.Nat.Base hiding (_·_)
open import Cubical.Data.Nat.Order 
open import Cubical.Data.Fin 
open import Cubical.Data.Int
open import Cubical.Data.Sigma

open import Braid.BraidGroup
open import Braid.PureBraid



PBraid≤Braid : {n : ℕ} (b : BPureBraid n) → Braid n
PBraid≤Braid base = base
PBraid≤Braid (gen p q i) = gen p i
PBraid≤Braid (identity p i j) = commutativity p p (toℕ p , λ i₁ → {!toℕ p !}) i {! j !}
PBraid≤Braid (genEquality p q i j) = commutativity p q (toℕ p , {! !}) i {!  j !}


PBraid≤Braid (twoGenCommutativity1 p q r s proof-rp proof-sp proof-rq proof-sq i j) = commutativity {! r  !} {!p   !} {! proof-rp  !} i j
PBraid≤Braid (twoGenCommutativity2 p q r s proof-pr proof-ps proof-rq proof-sq i j) = commutativity p r {!  proof-pr !} i j
PBraid≤Braid (threeGenCommutativityConnector r p q proof-rp proof-pq i) = pullThroughMid r (toℕ p , {!    ≤-suc (snd proof-rp) !}) i
PBraid≤Braid (threeGenCommutativityLeft r p q proof-rp proof-pq i j) =  pullThroughTop (toℕ r , {!   !}) (toℕ p , {!   !}) i {!  j !}
PBraid≤Braid (threeGenCommutativityMiddle r p q proof-rp proof-pq i j) = pullThroughTop {!   !} {!   !} {!   !} {!   !} 
PBraid≤Braid (threeGenCommutativityRight r p q proof-rp proof-pq i j) = {!   !}
PBraid≤Braid (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) = pullThroughMid {!   !} {!   !} {!   !}
PBraid≤Braid (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) = {!   !}
PBraid≤Braid (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) = {!   !}
  