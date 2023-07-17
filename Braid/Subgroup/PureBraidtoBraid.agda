{-# OPTIONS --safe #-}

module Braid.Subgroup.PureBraidtoBraid where

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude 
open import Cubical.Data.Nat
open import Cubical.Data.Fin 
open import Cubical.Data.Int

open import Braid.BraidGroup
open import Braid.PureBraid



PBraid≤Braid : {n : ℕ} (b : BPureBraid n) → Braid n
PBraid≤Braid base = base
PBraid≤Braid (gen p q i) = {!   !} 
PBraid≤Braid (identity p i j) = {!  !}
PBraid≤Braid (genEquality p q i j) = {!   !}


PBraid≤Braid (twoGenCommutativity1 p q r s proof-rp proof-sp proof-rq proof-sq i j) = {!   !}
PBraid≤Braid (twoGenCommutativity2 p q r s proof-pr proof-ps proof-rq proof-sq i j) = {!   !}
PBraid≤Braid (threeGenCommutativityConnector r p q proof-rp proof-pq i) = {!   !}
PBraid≤Braid (threeGenCommutativityLeft r p q proof-rp proof-pq i j) = {!   !}
PBraid≤Braid (threeGenCommutativityMiddle r p q proof-rp proof-pq i j) = {!   !}
PBraid≤Braid (threeGenCommutativityRight r p q proof-rp proof-pq i j) = {!   !}
PBraid≤Braid (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) = {!   !}
PBraid≤Braid (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) = {!   !}
PBraid≤Braid (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) = {!   !}
