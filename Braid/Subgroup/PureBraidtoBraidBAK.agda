{-# OPTIONS --safe #-}

module Braid.Subgroup.PureBraidtoBraid where

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude 
open import Cubical.Foundations.Path
open import Cubical.Data.Nat
open import Cubical.Data.Fin 
open import Cubical.Data.Nat.Order renaming (suc-≤-suc to sucP ; pred-≤-pred to pred ; suc-< to presuc ; ¬-<-zero to !<0 ; ¬m<m to !m<m ; <-weaken to weaken; <-asym to asym ; <-trans to trans ; <→≢  to <!=)
open import Cubical.Data.Empty as ⊥


open import Braid.BraidGroup
open import Braid.PureBraid

----------------------------------------------------------------------
{-
    Some helpers for order relations
-}

-- If r < p < q then r + 1 < q
zero-<-suc : (n : ℕ) → 0 < (suc n)
zero-<-suc n = ≤→< zero-≤ znots

sucTrans< : (r p q : ℕ) → (r < p) → (p < q) → ((suc r) < q)
sucTrans< r p zero proof-rp proof-pq = ⊥.rec {A = (suc r) < 0} (!<0 proof-pq)
sucTrans< r p (suc q) proof-rp proof-pq = ≤-trans (sucP proof-rp) proof-pq

m-<-sucm : (m : ℕ) → m < (suc m)
m-<-sucm zero = zero-<-suc 0
m-<-sucm (suc m) = sucP (m-<-sucm m)

-----------------------------------------------------------------------
module _ {ℓ : Level} {A : Type ℓ}
  {a₀₀ a₀₁ : A} {a₀₋ : a₀₀ ≡ a₀₁}
  {a₁₀ a₁₁ : A} {a₁₋ : a₁₀ ≡ a₁₁}
  {a₂₀ a₂₁ : A} {a₂₋ : a₂₀ ≡ a₂₁}
  {a₃₀ a₃₁ : A} {a₃₋ : a₃₀ ≡ a₃₁}
  {a₋₀ : a₀₀ ≡ a₁₀} {a₋₁ : a₀₁ ≡ a₁₁}
  {b₋₀ : a₁₀ ≡ a₂₀} {b₋₁ : a₁₁ ≡ a₂₁}
  {c₋₀ : a₂₀ ≡ a₃₀} {c₋₁ : a₂₁ ≡ a₃₁}

  where
-- "Threeway "Pointwise" composition
  _∙v_∙v_ : (p : Square a₀₋ a₁₋ a₋₀ a₋₁) (q : Square a₁₋ a₂₋ b₋₀ b₋₁) (r : Square a₂₋ a₃₋ c₋₀ c₋₁)
       → Square a₀₋ a₃₋ (a₋₀ ∙∙ b₋₀ ∙∙ c₋₀) (a₋₁ ∙∙ b₋₁ ∙∙ c₋₁)
  (p ∙v q ∙v r) i j = ((λ i → p i j) ∙∙ (λ i → q i j) ∙∙ (λ i → r i j)) i

-----------------------------------------------------------------------



-----------------------------------------------------------------------

Gen_^_ : {n : ℕ} (p : Fin n) (k : ℕ)  → Path (Braid n) base base -- composes a generator with itself k times
Gen p ^ zero = refl
Gen p ^ (suc zero) = gen p
Gen p ^ (suc (suc k)) = gen p ∙ (Gen p ^ (suc k))

Gen_^-_ : {n : ℕ} (p : Fin n) (k : ℕ)  → Path (Braid n) base base -- composes the inverse of a generator with itself k times
Gen p ^- zero = refl
Gen p ^- (suc zero) = sym (gen p)
Gen p ^- (suc (suc k)) = sym (gen p) ∙ (Gen p ^- (suc k))



GenHelperZero : {n : ℕ} (q : ℕ) → (q < (suc n)) → Path (Braid n) base base
{-

when p = 0 i.e A₀ₖ 
q and p are Fin (suc n) so that Pure Braid has n + 1 strands to match Braid n


3 base cases
-}
GenHelperZero zero proof-q = refl
GenHelperZero (suc zero) proof-q = gen (zero , pred proof-q) ∙ gen( zero , pred proof-q)
GenHelperZero (suc (suc q)) proof-q = gen (suc q , pred proof-q) ∙∙ GenHelperZero (suc q ) (presuc proof-q) ∙∙ (sym (gen (suc q , pred proof-q)))


GenConvertor : {n : ℕ}  →  (p q : Fin (suc n)) → (fst p < fst q) → Path (Braid n) base base
GenConvertor (zero , proof-p) q proof-pq = GenHelperZero (fst q) (snd q)
GenConvertor (suc p , proof-p) (zero , proof-q) proof-pq = ⊥.rec (!<0 proof-pq)

GenConvertor {n = zero} (suc p , proof-p) (suc q , proof-q) proof-pq = ⊥.rec (!<0 (pred proof-q))
GenConvertor {n = suc n} (suc p , proof-p) (suc q , proof-q) proof-pq i = addGen {n = n} (GenConvertor {n = n} (p , pred proof-p) (q , pred proof-q) (pred proof-pq) i)


SwapCompositions1 : {n : ℕ} → (p q : Fin n)
                            → ((suc (fst p)) < (fst q)) -- condition for commutativity 1
                            → Square 
                                (gen p) 
                                (gen p)
                                (Gen q ^ 2)
                                (Gen q ^ 2) 
                    

{-
   
                   σⱼ                                σⱼ²
               b - - - > b                       b - - - > b
               ^         ^                       ^         ^
          σᵢ   |         |  σᵢ        --->   σᵢ  |         | σᵢ
               |         |                       |         |
               b — — — > b                       b - - - > b    
                  σⱼ                                 σⱼ²
-}   
-- using vertical composition to get the required square
SwapCompositions1 p q proof-pq = (Braid.commutativity1 p q proof-pq) ∙v (Braid.commutativity1 p q proof-pq)


SwapCompositions2 : {n : ℕ} → (p q : Fin n)
                            → ((suc (fst q)) < (fst p)) -- condition for commutativity 1
                            → Square 
                                (gen p) 
                                (gen p)
                                (Gen q ^ 2)
                                (Gen q ^ 2) 
                    

{-
   
                   σⱼ                                σⱼ²
               b - - - > b                       b - - - > b
               ^         ^                       ^         ^
          σᵢ   |         |  σᵢ        --->   σᵢ  |         | σᵢ
               |         |                       |         |
               b — — — > b                       b - - - > b    
                  σⱼ                                 σⱼ²
-}   
-- using vertical composition to get the required square
SwapCompositions2 p q proof-pq = (Braid.commutativity2 p q proof-pq) ∙v (Braid.commutativity2 p q proof-pq)


commutativity1-Inv : {n : ℕ} (p q : Fin n) → (proof-pq : suc (toℕ p) < (toℕ q) ) → Square (Braid.gen p) (Braid.gen p) (sym (Braid.gen q)) (sym (Braid.gen q))
commutativity1-Inv p q proof-pq i j = commutativity1 p q proof-pq (~ i) j  

commutativity2-Inv : {n : ℕ} (p q : Fin n) → (proof-qp : suc (toℕ q) < (toℕ p) ) → Square (Braid.gen p) (Braid.gen p) (sym (Braid.gen q)) (sym (Braid.gen q))
commutativity2-Inv p q proof-qp i j = commutativity2 p q proof-qp (~ i) j  


GenSwapperZero : {n : ℕ} → (q : ℕ) → (proof-q : q < suc n)  -- p q are Fin (n+1) as PureBraid (n+1) has n+1 strands to match Braid n
                            → (r : Fin n)     -- r is Fin n as Braid n has n+1 strands                           
                            → (proof-pq : 0 < q) → (proof-qr : q < fst r)           -- condition for commutativity
                            → Square 
                                (gen r) 
                                (gen r)  
                                (GenConvertor (0 , zero-<-suc n) (q , proof-q) proof-pq)   -- Pure Braid generator in terms of combinations of Braid generators
                                (GenConvertor (0 , zero-<-suc n) (q , proof-q) proof-pq)
GenSwapperZero zero proof-q r proof-pq proof-qr = ⊥.rec (!<0 proof-pq)
GenSwapperZero (suc zero) proof-q r proof-pq proof-qr = SwapCompositions2 r (0 , pred proof-q) proof-qr
GenSwapperZero (suc (suc q)) proof-q r proof-pq proof-qr = 
    commutativity2 r (suc q , pred proof-q) proof-qr 
    ∙v GenSwapperZero (suc q) (presuc proof-q) r (zero-<-suc q) (presuc proof-qr) 
    ∙v commutativity2-Inv r (suc q , pred proof-q) proof-qr




-- this function can swap the image of a Pure Braid generator and a single Braid group generator
GenSwapper : {n : ℕ} → (p q r : ℕ) 
                      → (proof-p : p < (suc n)) → (proof-q : q < (suc n)) -- p q are Fin (n+1) as PureBraid (n+1) has n+1 strands to match Braid n
                      → (proof-r : r < n)                                 -- r is Fin n as Braid n has n+1 strands
                      → (proof-pq : p < q) → (proof-qr : q < r)           -- condition for commutativity
                      → Square  
                            (Braid.gen (r , proof-r)) 
                            (Braid.gen (r , proof-r)) 
                            (GenConvertor (p , proof-p)  (q , proof-q) proof-pq)   -- Pure Braid generator in terms of combinations of Braid generators
                            (GenConvertor (p , proof-p)  (q , proof-q) proof-pq)

GenSwapper zero q r proof-p proof-q proof-r proof-pq proof-qr = GenSwapperZero q proof-q (r , proof-r) proof-pq proof-qr
GenSwapper (suc p) zero r proof-p proof-q proof-r proof-pq proof-qr = ⊥.rec (!<0 proof-pq)

GenSwapper {n = zero} (suc p) (suc q) r proof-p proof-q proof-r proof-pq proof-qr = ⊥.rec (!<0 proof-r)

GenSwapper {n = suc n} (suc p) (suc q) r proof-p proof-q proof-r proof-pq proof-qr = {!   !}



-- GenSwapper {n = suc n} (suc p) (suc q) 0 proof-p proof-q proof-r proof-pq proof-qr = ⊥.rec (!<0 proof-qr)
-- GenSwapper {n = suc n} (suc p) (suc q) (suc zero) proof-p proof-q proof-r proof-pq proof-qr = ⊥.rec (!<0 (pred proof-qr))

-- GenSwapper {n = suc n} (suc p) (suc q) (suc (suc r)) proof-p proof-q proof-r proof-pq proof-qr  = {!   !}
-- {-
-- addGen {n = n} (GenSwapper {n = n} (p) (q) ((suc r)) (pred proof-p ) (pred proof-q ) (pred proof-r ) (pred proof-pq)  (pred proof-qr)  i j)
--  gen (suc (suc r) , proof-r) j
-- addGen
--   (GenSwapper p q (suc r) (pred proof-p) (pred proof-q)
--    (pred proof-r) (pred proof-pq) (pred proof-qr) i1 j)

-- -}




-- -- r < s < p < q

-- Commutativity1Zero : {n : ℕ} → (p q s : ℕ) -- r is zero 
--                     → (p < (suc n)) → (q < (suc n)) → (s < (suc n))   -- proofs to make them fin n
--                     → (p < q)           -- since we use only one presentation of a generator
--                     → (s < p)           -- condition for commutativity 1
--                     → (Path (Braid n) base base)

-- Commutativity1Zero p q zero proof-p proof-q proof-s proof-pq proof-sp = GenConvertor  p q proof-p proof-q proof-pq -- A rs does not exist so

-- Commutativity1Zero {n = n} zero zero (suc s) proof-p proof-q proof-s proof-pq proof-sp = ⊥.rec (!<0 proof-sp) -- these cases cannot exist as s < p but not if p = 0
-- Commutativity1Zero {n = n} zero (suc q) (suc s) proof-p proof-q proof-s proof-pq proof-sp = ⊥.rec (!<0 proof-sp)
-- Commutativity1Zero {n = n} (suc p) zero (suc s) proof-p proof-q proof-s proof-pq proof-sp = ⊥.rec (!<0 proof-pq)


-- Commutativity1Zero (suc p) (suc q) (suc zero) proof-p proof-q proof-s proof-pq proof-sp = {!   !}

-- Commutativity1Zero (suc p) (suc q) (suc (suc s)) proof-p proof-q proof-s proof-pq proof-sp x = {!   !}

-- Commutativity1Helper : {n : ℕ}  →  (p q r s : ℕ) 
--                       → (p < n) → (q < n) → (r < n) → (s < n) -- proofs to make them fin n
--                       → (p < q) → (r < s)                     -- since we use only one presentation of a generator
--                       → (s < p)                               -- condition for commutativity 1
--                       → (Path (Braid n) base base)
-- Commutativity1Helper = {!   !}

-- -- A₁₃  = σ₂ σ₁² σ₂⁻¹   A₁₃ . A₄₅ =  σ₂ σ₁² σ₂⁻¹ . σ₄ σ₄
-- -- A₄₅  = σ₄ σ₄         A₄₅ . A₁₃ =  σ₄ σ₄ . σ₂ σ₁² σ₂⁻¹




-- PBraid≤Braid : {n : ℕ} (b : BPureBraid (suc n)) → Braid n
-- PBraid≤Braid base = base
-- PBraid≤Braid (gen p q proof-pq i) = GenConvertor (fst p) (fst q) (snd p) (snd q) proof-pq i
-- PBraid≤Braid (twoGencommutativity1 p q r s proof-rs proof-sp proof-pq i j) = {!   !}
-- PBraid≤Braid (twoGencommutativity2 p q r s proof-pr proof-rs proof-sq proof-pq i j) = {!   !}
-- PBraid≤Braid (threeGenCommutativityConnector r p q proof-rp proof-pq proof-rq i) = {!   !}
-- PBraid≤Braid (threeGenCommutativityLeft r p q proof-rp proof-pq proof-rq i j) = {!   !}
-- PBraid≤Braid (threeGenCommutativityMiddle r p q proof-rp proof-pq proof-rq i j) = {!   !}
-- PBraid≤Braid (threeGenCommutativityRight r p q proof-rp proof-pq proof-rq i j) = {!   !}
-- PBraid≤Braid (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq proof-rq proof-pq i) = {!   !}
-- PBraid≤Braid (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq proof-rq proof-pq i j) = {!   !}
-- PBraid≤Braid (fourGenCommutativity r p s q proof-rp proof-ps proof-sq proof-rs proof-rq proof-pq i j) = {!   !}
 
  