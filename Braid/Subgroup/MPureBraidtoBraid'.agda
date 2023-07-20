{-# OPTIONS --safe #-}

module Braid.Subgroup.MPureBraidtoBraid' where

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude 
open import Cubical.Data.Nat
open import Cubical.Data.Fin 
open import Cubical.Data.Int
open import Cubical.Data.Nat.Order renaming (pred-≤-pred to pred ; suc-< to presuc ; ¬-<-zero to !<0 ; ¬m<m to !m<m ; <-weaken to weaken; <-asym to asym ; <-trans to trans ; <→≢  to <!=)
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Empty as ⊥


open import Braid.BraidGroup
open import Braid.PureBraidAlt hiding (GenComposer)

GenComposer : {n : ℕ} (p q : Fin n) → Path (Braid n) base base
GenComposer p q = (gen p) ∙ (gen q)

-- when p = 0 i.e A₀ₖ
GenHelperZero : (n : ℕ) (q : ℕ) → (q < n) → Path (Braid n) base base

-- 3 base cases
GenHelperZero n zero proof-q = refl
GenHelperZero n (suc zero) proof-q = gen (zero , presuc proof-q) ∙ gen (zero , presuc proof-q)
GenHelperZero n (suc (suc q)) proof-q = gen (suc q , presuc proof-q) ∙∙ (GenHelperZero n (suc q) (presuc proof-q))  ∙∙ (sym (gen (suc q , presuc proof-q)))



GenConvertor : {n : ℕ}  →  (p : ℕ) → (q : ℕ) → (p < n) → (q < n) → (p < q) → Path (Braid n) base base

-- 3 base cases
GenConvertor {n = zero} p q proof-p proof-q proof-pq = ⊥.rec {A = Path (Braid zero) base base} (!<0 proof-q)

GenConvertor {n = suc n} zero q proof-p proof-q proof-pq = GenHelperZero (suc n) q proof-q

GenConvertor {n = suc n} (suc p) zero proof-p proof-q proof-pq i = ⊥.rec {A = Path (Braid (suc n)) base base} (!<0 proof-pq) i

GenConvertor {n = suc n} (suc p) (suc q) proof-p proof-q proof-pq i =  addGen {n = n} (GenConvertor {n = n} p q (pred proof-p) (pred proof-q) (pred proof-pq) i) 



Commutativity1Helper : {n : ℕ}  →  (p q r s : ℕ) 
                      → (p < n) → (q < n) → (r < n) → (s < n) -- proofs to make them fin n
                      → (p < q) → (r < s)                     -- to use only one presentation of a generator
                      → (Path (Braid n) base base)
Commutativity1Helper = {!   !}

-- A₁₃  = σ₂ σ₁² σ₂⁻¹   A₁₃ . A₄₅ =  σ₂ σ₁² σ₂⁻¹ . σ₄ σ₄
-- A₄₅  = σ₄ σ₄         A₄₅ . A₁₃ =  σ₄ σ₄ . σ₂ σ₁² σ₂⁻¹




PBraid≤Braid : {n : ℕ} (b : BPureBraid' n) → Braid n
PBraid≤Braid base = base
PBraid≤Braid (gen (p , proof-p) (q , proof-q) constraint i) = GenConvertor p q proof-p proof-q constraint i

PBraid≤Braid (twoGencommutativity1 p q r s proof-rs proof-sp proof-pq i j) = {!   !}





PBraid≤Braid (twoGencommutativity2 p q r s proof-pr proof-rs proof-sq proof-pq i j) = {!   !}
PBraid≤Braid (threeGenCommutativityConnector r p q proof-rp proof-pq proof-rq i) = {!   !}
PBraid≤Braid (threeGenCommutativityLeft r p q proof-rp proof-pq proof-rq i j) = {!   !}
PBraid≤Braid (threeGenCommutativityMiddle r p q proof-rp proof-pq proof-rq i j) = {!   !}
PBraid≤Braid (threeGenCommutativityRight r p q proof-rp proof-pq proof-rq i j) = {!   !}
PBraid≤Braid (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq proof-rq proof-pq i) = {!   !}
PBraid≤Braid (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq proof-rq proof-pq i j) = {!   !}
PBraid≤Braid (fourGenCommutativity r p s q proof-rp proof-ps proof-sq proof-rs proof-rq proof-pq i j) = {!   !}