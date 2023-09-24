{-

Changed working definition of pure braid to one with constraints to avoid 
using trichotomy. This one uses trichotomy, so it was abandoned.




-}








{-# OPTIONS --safe #-}

module Braid.Subgroup.MPureBraidtoBraid where

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude 
open import Cubical.Data.Nat
open import Cubical.Data.Fin 
open import Cubical.Data.Int
open import Cubical.Data.Nat.Order renaming (pred-≤-pred to pred ; suc-< to presuc ; ¬-<-zero to !<0 ; ¬m<m to !m<m ; <-weaken to weaken; <-asym to asym ; <-trans to trans ; <→≢  to <!=)
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Empty as ⊥


open import Braid.BraidGroup
open import Braid.PureBraid


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

GenConvertor {n = suc n} (suc p) (suc q) proof-p proof-q proof-pq i = addGen {n = n} (GenConvertor {n = n} p q (pred proof-p) (pred proof-q) (pred proof-pq) i) 



CommutativityHelperZero : (n : ℕ)  →  (p q s : ℕ)              --  
                      → (p < n) → (q < n) → (s < n)             -- proofs to make them fin n
                      → (p < q)                                 -- to use only one presentation a generator
                      → (s < p) → (s < q)   -- conditions for commutativity
                      → (Path (Braid n) base base)
CommutativityHelperZero = ?






CommutativityHelper : {n : ℕ}  →  (p q r s : ℕ) 
                      → (p < n) → (q < n) → (r < n) → (s < n) -- proofs to make them fin n
                      → (p < q) → (r < s)                     -- to use only one presentation a generator
                      → (r < p) → (r < q) → (s < p) → (s < q)                              -- conditions for commutativity
                      → (Path (Braid n) base base)
                      
CommutativityHelper zero zero zero zero p-a p-b p-c p-d ab cd ca cb da db = {!   !}
CommutativityHelper zero zero zero (suc d) p-a p-b p-c p-d ab cd ca cb da db = {!   !}
CommutativityHelper zero zero (suc c) zero p-a p-b p-c p-d ab cd ca cb da db = {!   !}
CommutativityHelper zero zero (suc c) (suc d) p-a p-b p-c p-d ab cd ca cb da db = GenConvertor (suc c) (suc d) p-c p-d cd
CommutativityHelper zero (suc b) zero zero p-a p-b p-c p-d ab cd ca cb da db = {!   !}
CommutativityHelper zero (suc b) zero (suc d) p-a p-b p-c p-d ab cd ca cb da db = {!   !}
CommutativityHelper zero (suc b) (suc c) zero p-a p-b p-c p-d ab cd ca cb da db = {!   !}
CommutativityHelper zero (suc b) (suc c) (suc d) p-a p-b p-c p-d ab cd ca cb da db = GenConvertor (suc c) (suc d) p-c p-d cd
CommutativityHelper (suc a) zero zero zero p-a p-b p-c p-d ab cd ca cb da db = {!   !}
CommutativityHelper (suc a) zero zero (suc d) p-a p-b p-c p-d ab cd ca cb da db = {!   !}
CommutativityHelper (suc a) zero (suc c) zero p-a p-b p-c p-d ab cd ca cb da db = {!   !}
CommutativityHelper (suc a) zero (suc c) (suc d) p-a p-b p-c p-d ab cd ca cb da db = GenConvertor (suc c) (suc d) p-c p-d cd
CommutativityHelper (suc a) (suc b) zero zero p-a p-b p-c p-d ab cd ca cb da db = GenConvertor (suc a) (suc b) p-a p-b ab
CommutativityHelper (suc a) (suc b) zero (suc d) p-a p-b p-c p-d ab cd ca cb da db = GenConvertor (suc a) (suc b) p-a p-b ab
CommutativityHelper (suc a) (suc b) (suc c) zero p-a p-b p-c p-d ab cd ca cb da db = GenConvertor (suc a) (suc b) p-a p-b ab
CommutativityHelper (suc a) (suc b) (suc c) (suc d) p-a p-b p-c p-d ab cd ca cb da db = {!   !}

-- A₁₃  = σ₂ σ₁² σ₂⁻¹   A₁₃ . A₄₅ =  σ₂ σ₁² σ₂⁻¹ . σ₄ σ₄
-- A₄₅  = σ₄ σ₄         A₄₅ . A₁₃ =  σ₄ σ₄ . σ₂ σ₁² σ₂⁻¹






PBraid≤Braid : {n : ℕ} (b : BPureBraid n) → Braid n
PBraid≤Braid base = base


PBraid≤Braid (gen (p , proof-p) (q , proof-q) i) with p ≟ q
... | (lt proof) = GenConvertor p q proof-p proof-q proof i
... | (eq proof) = base
... | (gt proof) = GenConvertor q p proof-q proof-p proof i -- since Aᵢⱼ = Aⱼᵢ for any i j


PBraid≤Braid (identity p i j) with fst p ≟ fst p
... | (lt proof) = ⊥.rec {A = Square (GenConvertor (fst p) (fst p) (snd p) (snd p) proof) refl refl refl } (!m<m proof) i j 
... | (eq proof) = base
... | (gt proof) = ⊥.rec {A = Square (GenConvertor (fst p) (fst p) (snd p) (snd p) proof) refl refl refl } (!m<m proof) i j 



PBraid≤Braid (genEquality p q i j) with fst p ≟ fst q | fst q ≟ fst p
... | (lt proof) | (lt proof2) = ⊥.rec {A = Square (GenConvertor (fst p) (fst q) (snd p) (snd q) proof) (GenConvertor (fst q) (fst p) (snd q) (snd p) proof2) refl refl} (asym proof (weaken proof2)) i j
... | (lt proof) | (eq proof2) = ⊥.rec {A = Square (GenConvertor (fst p) (fst q) (snd p) (snd q) proof) refl refl refl} (<!= proof (sym proof2)) i j
... | (lt proof) | (gt proof2) = GenConvertor (fst p) (fst q) (snd p) (snd q) (isProp≤ proof proof2 i) j

     
... | (eq proof) | (lt proof2) = ⊥.rec {A = Square refl (GenConvertor (fst q) (fst p) (snd q) (snd p) proof2) refl refl} (<!= proof2 (sym proof)) i j
... | (eq proof) | (eq proof2) = base
... | (eq proof) | (gt proof2) = ⊥.rec {A = Square refl (GenConvertor (fst p) (fst q) (snd p) (snd q) proof2) refl refl} (<!= proof2 proof) i j


... | (gt proof) | (lt proof2) = GenConvertor (fst q) (fst p) (snd q) (snd p) (isProp≤ proof proof2 i) j
... | (gt proof) | (eq proof2) = ⊥.rec {A = Square (GenConvertor (fst q) (fst p) (snd q) (snd p) proof) refl refl refl} (<!= proof proof2) i j
... | (gt proof) | (gt proof2) = ⊥.rec {A = Square(GenConvertor (fst q) (fst p) (snd q) (snd p) proof) (GenConvertor (fst p) (fst q) (snd p) (snd q) proof2) refl refl} (asym proof (weaken proof2)) i j


--                                                         GenConvertor (fst r) (fst s)
--                                                       b - - - - - - - - > b
--                         GenConvertor (fst p) (fst q)  /  ^                 / ^  GenConvertor (fst p) (fst q)   
--                                                  /    |      sym Apq  /   |
--                                                /      |             /     |
--                                               b - - - - - - - - > b       |
--                                               ^     GHelper r s   ^       |                    ^  j
--                                               |       |           |       |                  k | /
--                                               |       |           |       |                    ∙ — >
--                                               |       |           |       |                      i
--                                               |       b - - - - - | - - > b
--                                               |     /             |     /
--                                               |   /               |   /   
--                                               | /                 | /
--                                               b - - - - - - - - > b
--                                                      


PBraid≤Braid (twoGenCommutativity1 (fst₁ , snd₁) (fst₂ , snd₂) (fst₃ , snd₃) (fst₄ , snd₄) proof-rp proof-sp proof-rq proof-sq i j) = {!   !}
-- with fst p ≟ fst q | fst r ≟ fst s
-- ... | (lt proof) | (lt proof2) = commutativity p q {!   !} {!   !} {!   !} 

-- ... | (lt proof) | (eq proof2) =  GenConvertor (fst p) (fst q) (snd p) (snd q) proof j
-- ... | (lt proof) | (gt proof2) =  {!   !}

     
-- ... | (eq proof) | (lt proof2) =  GenConvertor (fst r) (fst s) (snd r) (snd s) proof2 i
-- ... | (eq proof) | (eq proof2) =  base
-- ... | (eq proof) | (gt proof2) =  GenConvertor (fst s) (fst r) (snd s) (snd r) proof2 i


-- ... | (gt proof) | (lt proof2) =  {!   !}
-- ... | (gt proof) | (eq proof2) =  GenConvertor (fst q) (fst p) (snd q) (snd p) proof j
-- ... | (gt proof) | (gt proof2) =  {!   !}


PBraid≤Braid (twoGenCommutativity2 p q r s proof-pr proof-ps proof-rq proof-sq i j) with fst p ≟ fst q | fst r ≟ fst s
... | (lt proof) | (lt proof2) = {!   !}
... | (lt proof) | (eq proof2) = GenConvertor (fst p) (fst q) (snd p) (snd q) proof j
... | (lt proof) | (gt proof2) = {!   !}

     
... | (eq proof) | (lt proof2) = GenConvertor (fst r) (fst s) (snd r) (snd s) proof2 i
... | (eq proof) | (eq proof2) = base
... | (eq proof) | (gt proof2) = GenConvertor (fst s) (fst r) (snd s) (snd r) proof2 i


... | (gt proof) | (lt proof2) = {!   !}
... | (gt proof) | (eq proof2) = GenConvertor (fst q) (fst p) (snd q) (snd p) proof j
... | (gt proof) | (gt proof2) = {!   !}



PBraid≤Braid (threeGenCommutativityConnector r p q i) = {!   !}
PBraid≤Braid (threeGenCommutativityComposition r p q proof-rp proof-pq i j) = {!   !}
PBraid≤Braid (threeGenCommutativity r p q proof-rp proof-pq i j) = {!   !}



PBraid≤Braid (fourGenCommutativityConnector r p s q i) = {!   !}
PBraid≤Braid (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) = {!   !}
PBraid≤Braid (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) = {!   !}
