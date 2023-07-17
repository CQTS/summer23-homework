{-# OPTIONS --safe #-}
module Braid.Isomorphism.function where

open import Cubical.Foundations.Prelude

open import Braid.PureBraidReducedConstraints
open import Braid.PureBraid
open import Cubical.Data.Nat.Order renaming (pred-≤-pred to pred ; <-weaken to weaken; <-asym to asym ; <-trans to trans ; <→≢ to <!=)
open import Cubical.Data.Nat
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Fin


BPureBraid→BPureBraid' : ∀ n → (b : BPureBraid n) → BPureBraid' n
BPureBraid→BPureBraid' n base = base
BPureBraid→BPureBraid' n (gen p q i) = gen p q i
BPureBraid→BPureBraid' n (identity p i j) = identity p i j
BPureBraid→BPureBraid' n (genEquality p q i j) = genEquality p q i j
BPureBraid→BPureBraid' n (twoGenCommutativity1 p q r s proof-rp proof-sp proof-rq proof-sq i j) = twoGenCommutativity1 p q r s proof-rp proof-sp proof-rq proof-sq i j
BPureBraid→BPureBraid' n (twoGenCommutativity2 p q r s proof-pr proof-ps proof-rq proof-sq i j) = twoGenCommutativity2 p q r s proof-pr proof-ps proof-rq proof-sq i j
BPureBraid→BPureBraid' n (threeGenCommutativityConnector r p q proof-rp proof-pq i) = threeGenCommutativityConnector r p q i
BPureBraid→BPureBraid' n (threeGenCommutativityLeft r p q proof-rp proof-pq i j) = threeGenCommutativityLeft r p q i j
BPureBraid→BPureBraid' n (threeGenCommutativityMiddle r p q proof-rp proof-pq i j) = threeGenCommutativityMiddle r p q i j
BPureBraid→BPureBraid' n (threeGenCommutativityRight r p q proof-rp proof-pq i j) = threeGenCommutativityRight r p q i j
BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) = fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i
BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) = fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j
BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) = fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j