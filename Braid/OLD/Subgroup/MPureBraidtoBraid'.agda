
{-
This file used unnecessary case splits
New copy was created without as many unneeded case splits
-}






{-# OPTIONS --safe #-}

module Braid.Subgroup.MPureBraidtoBraid' where

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude 
open import Cubical.Foundations.Path
open import Cubical.Data.Nat
open import Cubical.Data.Fin 
open import Cubical.Data.Int
open import Cubical.Data.Nat.Order renaming (pred-≤-pred to pred ; suc-< to presuc ; ¬-<-zero to !<0 ; ¬m<m to !m<m ; <-weaken to weaken; <-asym to asym ; <-trans to trans ; <→≢  to <!=)
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Empty as ⊥


open import Braid.BraidGroup
open import Braid.PureBraidAlt hiding (GenComposer)

----------------------------------------------------------------------
{-
    Some helpers for order relations
-}

-- If r < p < q then r + 1 < q
zero-<-suc : (n : ℕ) → 0 < (suc n)
zero-<-suc n = ≤→< zero-≤ znots

sucTrans< : (r p q : ℕ) → (r < p) → (p < q) → ((suc r) < q)
sucTrans< r p zero proof-rp proof-pq = ⊥.rec {A = (suc r) < 0} (!<0 proof-pq)
sucTrans< r p (suc q) proof-rp proof-pq = ≤-trans (suc-≤-suc proof-rp) proof-pq

-----------------------------------------------------------------------



GenComposer : {n : ℕ} (p q : Fin n) → Path (Braid n) base base
GenComposer p q = (gen p) ∙ (gen q)

-- when p = 0 i.e A₀ₖ
GenHelperZero : (n : ℕ) (q : ℕ) → (q < n) → Path (Braid n) base base

-- 3 base cases
GenHelperZero n zero proof-q = refl
GenHelperZero n (suc zero) proof-q = GenComposer (zero , presuc proof-q) (zero , presuc proof-q)
GenHelperZero n (suc (suc q)) proof-q = gen (suc q , presuc proof-q) ∙∙ (GenHelperZero n (suc q) (presuc proof-q))  ∙∙ (sym (gen (suc q , presuc proof-q)))

GenConvertor : {n : ℕ}  →  (p q : ℕ) → (p < n) → (q < n) → (p < q) → Path (Braid n) base base

-- 3 base cases
GenConvertor {n = zero} p q proof-p proof-q proof-pq = ⊥.rec {A = Path (Braid zero) base base} (!<0 proof-q)

GenConvertor {n = suc n} zero q proof-p proof-q proof-pq = GenHelperZero (suc n) q proof-q

GenConvertor {n = suc n} (suc p) zero proof-p proof-q proof-pq i = ⊥.rec {A = Path (Braid (suc n)) base base} (!<0 proof-pq) i

GenConvertor {n = suc n} (suc p) (suc q) proof-p proof-q proof-pq i =  addGen {n = n} (GenConvertor {n = n} p q (pred proof-p) (pred proof-q) (pred proof-pq) i) 




SwapCompositions : {n : ℕ} → (p q : ℕ) → (proof-p : p < n) → (proof-q : q < n) → ((suc p) < q) → 
    Square (gen (p , proof-p)) (gen (p , proof-p)) (GenComposer (q , proof-q) (q , proof-q)) (GenComposer (q , proof-q) (q , proof-q)) 
    
-- using vertical composition to get the required square-- using vertical composition to get the required square
SwapCompositions p q proof-p proof-q proof-pq = 
    (Braid.commutativity1 (p , proof-p) (q , proof-q) proof-pq) ∙v' (Braid.commutativity1 (p , proof-p) (q , proof-q) proof-pq)




GenSwapper : {n : ℕ} → (p q r : ℕ) → (proof-p : p < n) → (proof-q : q < n) → (proof-r : r < n) → (proof-pq : p < q) → (proof-qr : q < r) →
    Square (gen (r , proof-r)) (gen (r , proof-r)) (GenConvertor p q proof-p proof-q proof-pq) (GenConvertor p q proof-p proof-q proof-pq) 

GenSwapper zero zero r proof-p proof-q proof-r proof-pq proof-qr = ⊥.rec {A = Square (gen (r , proof-r)) (gen (r , proof-r))
                                                                                            (GenConvertor zero zero proof-p proof-q proof-pq)
                                                                                            (GenConvertor zero zero proof-p proof-q proof-pq)
                                                                            } (!<0 proof-pq)

GenSwapper zero (suc zero) r proof-p proof-q proof-r proof-pq proof-qr = λ i j → {! ? ∙v' ? i j  !}

GenSwapper zero (suc (suc q)) r proof-p proof-q proof-r proof-pq proof-qr = {!   !}
GenSwapper (suc p) zero r proof-p proof-q proof-r proof-pq proof-qr = {!   !}


GenSwapper (suc p) (suc q) r proof-p proof-q proof-r proof-pq proof-qr = {!   !}









-- r < s < p < q

Commutativity1Zero : {n : ℕ} → (p q s : ℕ) -- r is zero 
                    → (p < n) → (q < n) → (s < n)   -- proofs to make them fin n
                    → (p < q)           -- since we use only one presentation of a generator
                    → (s < p)           -- condition for commutativity 1
                    → (Path (Braid n) base base)

Commutativity1Zero p q zero proof-p proof-q proof-s proof-pq proof-sp = GenConvertor  p q proof-p proof-q proof-pq -- A rs does not exist so

Commutativity1Zero {n = n} zero zero (suc s) proof-p proof-q proof-s proof-pq proof-sp = ⊥.rec {A = Path (Braid n) base base} (!<0 proof-sp) -- these cases cannot exist as s < p but not if p = 0
Commutativity1Zero {n = n} zero (suc q) (suc s) proof-p proof-q proof-s proof-pq proof-sp = ⊥.rec {A = Path (Braid n) base base} (!<0 proof-sp)
Commutativity1Zero {n = n} (suc p) zero (suc s) proof-p proof-q proof-s proof-pq proof-sp = ⊥.rec {A = Path (Braid n) base base} (!<0 proof-pq)


Commutativity1Zero (suc p) (suc q) (suc zero) proof-p proof-q proof-s proof-pq proof-sp = {!   !}

Commutativity1Zero (suc p) (suc q) (suc (suc s)) proof-p proof-q proof-s proof-pq proof-sp = {!   !}

Commutativity1Helper : {n : ℕ}  →  (p q r s : ℕ) 
                      → (p < n) → (q < n) → (r < n) → (s < n) -- proofs to make them fin n
                      → (p < q) → (r < s)                     -- since we use only one presentation of a generator
                      → (s < p)                               -- condition for commutativity 1
                      → (Path (Braid n) base base)
Commutativity1Helper = {!   !}

-- A₁₃  = σ₂ σ₁² σ₂⁻¹   A₁₃ . A₄₅ =  σ₂ σ₁² σ₂⁻¹ . σ₄ σ₄
-- A₄₅  = σ₄ σ₄         A₄₅ . A₁₃ =  σ₄ σ₄ . σ₂ σ₁² σ₂⁻¹




PBraid≤Braid : {n : ℕ} (b : BPureBraid' (suc n)) → Braid n
PBraid≤Braid base = base

PBraid≤Braid {n = zero} (gen (p , proof-p) (zero , proof-q) proof-pq i) = ⊥.rec {A = Path (Braid zero) base base} (!<0 proof-pq) i
PBraid≤Braid {n = zero} (gen (p , proof-p) (suc q , proof-q) proof-pq i) = ⊥.rec {A = Path (Braid zero) base base} (!<0 (pred proof-q)) i

PBraid≤Braid {n = suc n} (gen (p , proof-p) (zero , proof-q) proof-pq i) = ⊥.rec {A = Path (Braid (suc n)) base base} (!<0 proof-pq) i

PBraid≤Braid {n = suc n} (gen (zero , proof-p) (suc q , proof-q) proof-pq i) = GenConvertor zero (suc q) (zero-<-suc n) {!   !} {!   !} i

PBraid≤Braid {n = suc n} (gen (suc p , proof-p) (suc q , proof-q) proof-pq i) = {!   !}



-- PBraid≤Braid {n = (suc n)} (gen (zero , proof-p) (zero , proof-q) proof-pq i)  = ⊥.rec {A = Path (Braid n) base base} (⊥.rec (!<0 proof-pq)) i
-- PBraid≤Braid {n = (suc n)} (gen (suc p , proof-p) (zero , proof-q) proof-pq i) = ⊥.rec {A = Path (Braid n) base base} (⊥.rec (!<0 proof-pq)) i

-- PBraid≤Braid (gen (zero , proof-p) (suc q , proof-q) proof-pq i) = GenConvertor zero (suc q) (≤→< {!   !} {!   !}) {!   !} {!   !} i
-- PBraid≤Braid (gen (suc p , proof-p) (suc q , proof-q) proof-pq i) = {!   !}

PBraid≤Braid (twoGencommutativity1 p q r s proof-rs proof-sp proof-pq i i₁) = {!   !}
PBraid≤Braid (twoGencommutativity2 p q r s proof-pr proof-rs proof-sq proof-pq i i₁) = {!   !}
PBraid≤Braid (threeGenCommutativityConnector r p q proof-rp proof-pq proof-rq i) = {!   !}
PBraid≤Braid (threeGenCommutativityLeft r p q proof-rp proof-pq proof-rq i i₁) = {!   !}
PBraid≤Braid (threeGenCommutativityMiddle r p q proof-rp proof-pq proof-rq i i₁) = {!   !}
PBraid≤Braid (threeGenCommutativityRight r p q proof-rp proof-pq proof-rq i i₁) = {!   !}
PBraid≤Braid (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq proof-rq proof-pq i) = {!   !}
PBraid≤Braid (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq proof-rq proof-pq i i₁) = {!   !}
PBraid≤Braid (fourGenCommutativity r p s q proof-rp proof-ps proof-sq proof-rs proof-rq proof-pq i i₁) = {!   !}
