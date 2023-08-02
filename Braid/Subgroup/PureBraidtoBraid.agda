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

---------------------------------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------------------------------
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

squeezeTheorem : {a n : ℕ} → (n < a) → (a < suc n) → ⊥
squeezeTheorem {a = zero} {n = n} proof-na proof-asucn = !<0 proof-na
squeezeTheorem {a = suc a} {n = zero} proof-na proof-asucn = !<0 (pred proof-asucn)
squeezeTheorem {a = suc a} {n = suc n} proof-na proof-asucn = squeezeTheorem {a = a} {n = n} (pred proof-na) (pred proof-asucn)


squeezeTheorem2 : {a b n : ℕ} → (n < a) → (a < b) → (b < (suc (suc n))) → ⊥
squeezeTheorem2 {a = zero} {b = b} {n = n} proof-na proof-ab proof-bsucn = !<0 proof-na
squeezeTheorem2 {a = suc a} {b = zero} {n = n} proof-na proof-ab proof-bsucn = !<0 proof-ab

squeezeTheorem2 {a = suc a} {b = suc b} {n = zero} proof-na proof-ab proof-bsucn = !<0 (pred (pred (sucTrans< (suc a) (suc b) (2) proof-ab proof-bsucn)))
squeezeTheorem2 {a = suc a} {b = suc b} {n = suc n} proof-na proof-ab proof-bsucn = 
    squeezeTheorem2 {a = a} {b = b} {n = n} (pred proof-na) (pred proof-ab) (pred proof-bsucn)
---------------------------------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------------------------------
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
  _∙∙v_∙∙v_ : (p : Square a₀₋ a₁₋ a₋₀ a₋₁) (q : Square a₁₋ a₂₋ b₋₀ b₋₁) (r : Square a₂₋ a₃₋ c₋₀ c₋₁)
       → Square a₀₋ a₃₋ (a₋₀ ∙∙ b₋₀ ∙∙ c₋₀) (a₋₁ ∙∙ b₋₁ ∙∙ c₋₁)
  (p ∙∙v q ∙∙v r) i j = ((λ i → p i j) ∙∙ (λ i → q i j) ∙∙ (λ i → r i j)) i
---------------------------------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------------------------------



---------------------------------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------------------------------
commutativity1-Inv : {n : ℕ} (p q : Fin n) → (proof-pq : suc (toℕ p) < (toℕ q) ) → Square (Braid.gen p) (Braid.gen p) (sym (Braid.gen q)) (sym (Braid.gen q))
commutativity1-Inv p q proof-pq i j = commutativity1 p q proof-pq (~ i) j  

commutativity2-Inv : {n : ℕ} (p q : Fin n) → (proof-qp : suc (toℕ q) < (toℕ p) ) → Square (Braid.gen p) (Braid.gen p) (sym (Braid.gen q)) (sym (Braid.gen q))
commutativity2-Inv p q proof-qp i j = commutativity2 p q proof-qp (~ i) j  
---------------------------------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------------------------------


---------------------------------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------------------------------
Gen_^_ : {n : ℕ} (p : Fin n) (k : ℕ)  → Path (Braid n) base base -- composes a generator with itself k times
Gen p ^ zero = refl
Gen p ^ (suc zero) = gen p
Gen p ^ (suc (suc k)) = gen p ∙ (Gen p ^ (suc k))

Gen_^-_ : {n : ℕ} (p : Fin n) (k : ℕ)  → Path (Braid n) base base -- composes the inverse of a generator with itself k times
Gen p ^- zero = refl
Gen p ^- (suc zero) = sym (gen p)
Gen p ^- (suc (suc k)) = sym (gen p) ∙ (Gen p ^- (suc k))
---------------------------------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------------------------------



---------------------------------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------------------------------
{-
                                            CONVERTING PURE BRAID GENERATOR Apq 
                                            TO ITS REPRESENTATIONS AS COMBINATIONS
                                            OF BRAID GENERATORS σₖ
                                            
-}

{-
when p = 0 i.e A₀ₖ 
q and p are Fin (suc n) so that Pure Braid has n + 1 strands to match Braid n
-}
GenHelperZero : {n : ℕ} (q : ℕ) → (q < (suc n)) → Path (Braid n) base base

GenHelperZero zero proof-q = refl
GenHelperZero (suc zero) proof-q = gen (zero , pred proof-q) ∙ gen( zero , pred proof-q)
GenHelperZero (suc (suc q)) proof-q = gen (suc q , pred proof-q) 
                                        ∙∙ GenHelperZero (suc q ) (presuc proof-q) 
                                        ∙∙ (sym (gen (suc q , pred proof-q)))


GenConvertor : {n : ℕ}  →  (p q : ℕ) → (p < (suc n)) → (q < (suc n)) → (p < q) → Path (Braid n) base base

GenConvertor zero q proof-p proof-q proof-pq = GenHelperZero q proof-q
GenConvertor (suc p) zero proof-p proof-q proof-pq = ⊥.rec (!<0 proof-pq)

GenConvertor {zero} (suc p) (suc q) proof-p proof-q proof-pq = ⊥.rec (!<0 (pred proof-q))
GenConvertor {n = suc n} (suc p) (suc q) proof-p proof-q proof-pq i = 
    addGen {n = n} (GenConvertor {n = n} p q (pred proof-p) (pred proof-q) (pred proof-pq) i)
---------------------------------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------------------------------





---------------------------------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------------------------------


 {-
   
                   σⱼ                                σⱼ²
               b - - - > b                       b - - - > b
               ^         ^                       ^         ^
          σᵢ   |         |  σᵢ        --->   σᵢ  |         | σᵢ
               |         |                       |         |
               b — — — > b                       b - - - > b    
                  σⱼ                                 σⱼ²
-}   

Commutativity1Composition : {n : ℕ} → (p q : ℕ)
                            → (proof-p : p < n) → (proof-q : q < n) --proofs to make them Fin n
                            → ((suc p) < q) -- condition for commutativity 1
                            → Square 
                                (gen (p , proof-p)) 
                                (gen (p , proof-p))
                                (Gen (q , proof-q) ^ 2)
                                (Gen (q , proof-q) ^ 2) 
    

-- using horizontal composition to get the required square
Commutativity1Composition p q proof-p proof-q proof-pq = 
    (Braid.commutativity1 (p , proof-p) (q , proof-q) proof-pq) ∙v (Braid.commutativity1 (p , proof-p) (q , proof-q) proof-pq)

---------------------------------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------------------------------



---------------------------------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------------------------------


Commutativity2Composition : {n : ℕ} → (p q : ℕ) 
                            → (proof-p : p < n) → (proof-q : q < n)  -- proofs to make them Fin n
                            → ((suc q) < p)                          -- condition for commutativity2
                            → Square 
                                (gen (p , proof-p)) 
                                (gen (p , proof-p)) 
                                (Gen (q , proof-q) ^ 2) 
                                (Gen (q , proof-q) ^ 2)
                  
Commutativity2Composition p q proof-p proof-q proof-qp =
     (Braid.commutativity2 (p , proof-p) (q , proof-q) proof-qp) ∙v (Braid.commutativity2 (p , proof-p) (q , proof-q) proof-qp)


---------------------------------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------------------------------





---------------------------------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------------------------------
-- Proof that the image of Apq commutes with σ₀

GenSwapper1Zero : {n : ℕ} → (p q : ℕ) 
                            → (proof-p : p < (suc n)) → (proof-q : q < (suc n)) -- p q are Fin (n+1) as PureBraid (n+1) has n+1 strands to match Braid n
                            → (proof-r : 0 < n)                                 -- r is Fin n as Braid n has n+1 strands
                            → (proof-rp : suc 0 < p) →  (proof-pq : p < q)            -- condition for commutativity
                            → Square  
                                    (GenConvertor p q proof-p proof-q proof-pq)   -- Pure Braid generator in terms of combinations of Braid generators
                                    (GenConvertor p q proof-p proof-q proof-pq)
                                    (Braid.gen (0 , proof-r)) 
                                    (Braid.gen (0 , proof-r)) 
                                
GenSwapper1Zero zero q proof-p proof-q proof-r proof-rp proof-pq = ⊥.rec (!<0 proof-rp)
GenSwapper1Zero (suc zero) q proof-p proof-q proof-r proof-rp proof-pq = ⊥.rec (!m<m proof-rp)

GenSwapper1Zero (suc (suc zero)) q proof-p proof-q proof-r proof-rp proof-pq = {!   !}
GenSwapper1Zero (suc (suc (suc p))) q proof-p proof-q proof-r proof-rp proof-pq = {!   !}

---------------------------------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------------------------------


---------------------------------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------------------------------
-- Proof that Apq commutes with σᵣ . Useful when swapping with image of Aᵣᵣ₊₁
GenSwapper1 : {n : ℕ} → (p q r : ℕ) 
                            → (proof-p : p < (suc n)) → (proof-q : q < (suc n)) -- p q are Fin (n+1) as PureBraid (n+1) has n+1 strands to match Braid n
                            → (proof-r : r < n)                                 -- r is Fin n as Braid n has n+1 strands
                            → (proof-rp : suc r < p) →  (proof-pq : p < q)            -- condition for commutativity
                             → Square  
                                    (GenConvertor p q proof-p proof-q proof-pq)   -- Pure Braid generator in terms of combinations of Braid generators
                                    (GenConvertor p q proof-p proof-q proof-pq)
                                    (Braid.gen (r , proof-r)) 
                                    (Braid.gen (r , proof-r)) 
                                
GenSwapper1 p q zero proof-p proof-q proof-r proof-rp proof-pq = GenSwapper1Zero p q proof-p proof-q proof-r proof-rp proof-pq

GenSwapper1 zero q (suc r) proof-p proof-q proof-r proof-rp proof-pq = ⊥.rec (!<0 proof-rp)
GenSwapper1 1 q (suc r) proof-p proof-q proof-r proof-rp proof-pq = ⊥.rec (!<0 (pred proof-rp))
GenSwapper1 2 q (suc r) proof-p proof-q proof-r proof-rp proof-pq = ⊥.rec (!<0 (pred (pred proof-rp)))

GenSwapper1 3 4 (suc r) proof-p proof-q proof-r proof-rp proof-pq = {!   !}

GenSwapper1 3 (suc (suc (suc q))) (suc r) proof-p proof-q proof-r proof-rp proof-pq = {!   !}

GenSwapper1 (suc (suc (suc p))) q (suc r) proof-p proof-q proof-r proof-rp proof-pq = {!   !}

---------------------------------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------------------------------


---------------------------------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------------------------------
-- Proof that the image of A0q commutes with σᵣ

GenSwapper2Zero : {n : ℕ} → (q r : ℕ) 
                            → (proof-q : q < (suc n)) -- p q are Fin (n+1) as PureBraid (n+1) has n+1 strands to match Braid n
                            → (proof-r : r < n)                                 -- r is Fin n as Braid n has n+1 strands
                            → (proof-pq : 0 < q) → (proof-qr : q < r)           -- condition for commutativity
                            → Square 
                                (GenConvertor 0 q (zero-<-suc n) proof-q proof-pq)   -- Pure Braid generator in terms of combinations of Braid generators
                                (GenConvertor 0 q (zero-<-suc n) proof-q proof-pq)
                                (gen (r , proof-r)) 
                                (gen (r , proof-r))  
                                
GenSwapper2Zero zero r proof-q proof-r proof-pq proof-qr = ⊥.rec (!<0 proof-pq)
GenSwapper2Zero (suc zero) r proof-q proof-r proof-pq proof-qr i j  = (Commutativity2Composition r 0 proof-r (pred proof-q) proof-qr) j i
GenSwapper2Zero (suc (suc q)) r proof-q proof-r proof-pq proof-qr i j = 
    (commutativity2 (r , proof-r) (suc q , pred proof-q) proof-qr
    ∙∙v (λ i j → (GenSwapper2Zero (suc q) r (presuc proof-q) proof-r (zero-<-suc q) (presuc proof-qr)) j i)
    ∙∙v (commutativity2-Inv (r , proof-r) (suc q , pred proof-q) proof-qr)) j i

---------------------------------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------------------------------


---------------------------------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------------------------------

-- this function can swap the image of a Pure Braid generator and a single Braid group generator
-- useful when defining case (gen r r+1)
GenSwapper2 : {n : ℕ} → (p q r : ℕ) 
                      → (proof-p : p < (suc n)) → (proof-q : q < (suc n)) -- p q are Fin (n+1) as PureBraid (n+1) has n+1 strands to match Braid n
                      → (proof-r : r < n)                                 -- r is Fin n as Braid n has n+1 strands
                      → (proof-pq : p < q) → (proof-qr : q < r)           -- condition for commutativity
                      → Square  
                            (GenConvertor p q proof-p proof-q proof-pq)   -- Pure Braid generator in terms of combinations of Braid generators
                            (GenConvertor p q proof-p proof-q proof-pq)
                            (Braid.gen (r , proof-r)) 
                            (Braid.gen (r , proof-r)) 

GenSwapper2 zero q r proof-p proof-q proof-r proof-pq proof-qr = GenSwapper2Zero q r proof-q proof-r proof-pq proof-qr

GenSwapper2 (suc p) zero r proof-p proof-q proof-r proof-pq proof-qr = ⊥.rec (!<0 proof-pq)
GenSwapper2 {n = zero} (suc p) (suc q) r proof-p proof-q proof-r proof-pq proof-qr = ⊥.rec (!<0 proof-r)

GenSwapper2 {n = suc n} (suc p) (suc q) 0 proof-p proof-q proof-r proof-pq proof-qr = ⊥.rec (!<0 proof-qr)
GenSwapper2 {n = suc n} (suc p) (suc q) (suc zero) proof-p proof-q proof-r proof-pq proof-qr = ⊥.rec (!<0 (pred proof-qr))

GenSwapper2 {n = suc n} (suc p) (suc q) (suc (suc r)) proof-p proof-q proof-r proof-pq proof-qr i j  = 

            hcomp (λ  { k ( i = i0) → addGen ((GenConvertor p q (pred proof-p) (pred proof-q) (pred proof-pq) j))
                      ; k ( i = i1) → addGen ((GenConvertor p q (pred proof-p) (pred proof-q) (pred proof-pq) j))
                      ; k ( j = i0) → gen (suc (suc r) , isProp≤ ((sucP (pred proof-r))) proof-r k) i
                      ; k ( j = i1) → gen (suc (suc r) , isProp≤ ((sucP (pred proof-r))) proof-r k) i
                    }) 
            (addGen {n = n} ((GenSwapper2 {n = n} p q (suc r) (pred proof-p) (pred proof-q) (pred proof-r) (pred proof-pq) (pred proof-qr) i j)))

---------------------------------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------------------------------            


---------------------------------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------------------------------
GenSwapper3Zero  : {n : ℕ} → (q r : ℕ) 
                      → (proof-p : 0 < (suc n)) → (proof-q : q < (suc n)) -- p q are Fin (n+1) as PureBraid (n+1) has n+1 strands to match Braid n
                      → (proof-r : r < n)                                 -- r is Fin n as Braid n has n+1 strands
                      → (proof-pr : 0 < r) → (proof-rq : r < q) → (proof-pq : 0 < q)           -- condition for commutativity
                      → Square  
                            (GenConvertor 0 q proof-p proof-q proof-pq)   -- Pure Braid generator in terms of combinations of Braid generators
                            (GenConvertor 0 q proof-p proof-q proof-pq)
                            (Braid.gen (r , proof-r)) 
                            (Braid.gen (r , proof-r))
GenSwapper3Zero q zero proof-p proof-q proof-r proof-pr proof-rq proof-pq = ⊥.rec (!<0 proof-pr)
GenSwapper3Zero q (suc zero) proof-p proof-q proof-r proof-pr proof-rq proof-pq = {!   !}

GenSwapper3Zero q (suc (suc r)) proof-p proof-q proof-r proof-pr proof-rq proof-pq = {!   !}

GenSwapper3 : {n : ℕ} → (p q r : ℕ) 
                      → (proof-p : p < (suc n)) → (proof-q : q < (suc n)) -- p q are Fin (n+1) as PureBraid (n+1) has n+1 strands to match Braid n
                      → (proof-r : r < n)                                 -- r is Fin n as Braid n has n+1 strands
                      → (proof-pr : p < r) → (proof-rq : r < q) → (proof-pq : p < q)           -- condition for commutativity
                      → Square  
                            (GenConvertor p q proof-p proof-q proof-pq)   -- Pure Braid generator in terms of combinations of Braid generators
                            (GenConvertor p q proof-p proof-q proof-pq)
                            (Braid.gen (r , proof-r)) 
                            (Braid.gen (r , proof-r))

GenSwapper3 zero q r proof-p proof-q proof-r proof-pr proof-rq proof-pq = GenSwapper3Zero q r proof-p proof-q proof-r proof-pr proof-rq proof-pq
GenSwapper3 (suc p) zero r proof-p proof-q proof-r proof-pr proof-rq proof-pq = ⊥.rec (!<0 proof-rq)

GenSwapper3 (suc p) (suc q) zero proof-p proof-q proof-r proof-pr proof-rq proof-pq = ⊥.rec (!<0 proof-pr)
GenSwapper3 {n = zero} (suc p) (suc q) (suc r) proof-p proof-q proof-r proof-pr proof-rq proof-pq = ⊥.rec (!<0 proof-r)
GenSwapper3 {n = suc n} (suc p) (suc q) (suc r) proof-p proof-q proof-r proof-pr proof-rq proof-pq i j = 
            hcomp (λ  { k ( i = i0) → addGen ((GenConvertor p q (pred proof-p) (pred proof-q) (pred proof-pq) j))
                      ; k ( i = i1) → addGen ((GenConvertor p q (pred proof-p) (pred proof-q) (pred proof-pq) j))
                      ; k ( j = i0) → gen (suc r , isProp≤ (sucP (pred proof-r)) proof-r k) i
                      ; k ( j = i1) → gen (suc r , isProp≤ (sucP (pred proof-r)) proof-r k) i
                    }) 
            (addGen {n = n} (GenSwapper3 p q r (pred proof-p) (pred proof-q) (pred proof-r) (pred proof-pr) (pred proof-rq) (pred proof-pq) i j))


---------------------------------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------------------------------


---------------------------------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------------------------------

{-
               A r s
            b - - - > b
            ^         ^
      A p q |         |  A p q
            |         |
            b - - - > b
                A r s
                
-- r < s < p < q
-}


---------------------------------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------------------------------
Commutativity1Zero : {n : ℕ} (s p q : ℕ) -- r is zero
                    → (p-r : 0 < (suc n)) → (p-s : s < (suc n)) → (p-p : p < (suc n)) → (p-q : q < (suc n))    -- proofs to make them fin suc n
                    → (p-rs : 0 < s) → (s < p) → (p-pq : p < q)                 -- condition for commutativity 1
                    → Square 
                            (GenConvertor p q p-p p-q p-pq)
                            (GenConvertor p q p-p p-q p-pq)
                            (GenConvertor 0 s p-r p-s p-rs)
                            (GenConvertor 0 s p-r p-s p-rs)   

Commutativity1Zero zero p q proof-r proof-s proof-p proof-q proof-rs proof-sp proof-pq i j = GenConvertor p q proof-p proof-q proof-pq j

Commutativity1Zero (suc zero) p q proof-r proof-s proof-p proof-q proof-rs proof-sp proof-pq i j = 
    (GenSwapper1 p q zero proof-p proof-q (pred proof-s) proof-sp proof-pq ∙v GenSwapper1 p q zero proof-p proof-q (pred proof-s) proof-sp proof-pq) i j

Commutativity1Zero (suc (suc s)) p q proof-r proof-s proof-p proof-q proof-rs proof-sp proof-pq i j = 
    ( (GenSwapper1 p q (suc s) proof-p proof-q (pred proof-s) proof-sp proof-pq)
        ∙∙v (Commutativity1Zero (suc s) p q proof-r (presuc proof-s) proof-p proof-q (zero-<-suc s) (presuc proof-sp) proof-pq) 
            ∙∙v (λ i j → GenSwapper1 p q (suc s) proof-p proof-q (pred proof-s) proof-sp proof-pq (~ i) j)
    ) i j


Commutativity1Convertor : {n : ℕ} → (r s p q : ℕ)
                    → (p-r : r < (suc n)) → (p-s : s < (suc n)) → (p-p : p < (suc n)) → (p-q : q < (suc n))    -- proofss to make them fin suc n
                    → (p-rs : r < s) → (s < p) → (p-pq : p < q)                 -- condition for commutativity 1
                    → Square 
                            (GenConvertor p q p-p p-q p-pq)
                            (GenConvertor p q p-p p-q p-pq)
                            (GenConvertor r s p-r p-s p-rs)
                            (GenConvertor r s p-r p-s p-rs)   


Commutativity1Convertor zero s p q proof-r proof-s proof-p proof-q proof-rs proof-sp proof-pq = 
    Commutativity1Zero s p q proof-r proof-s proof-p proof-q proof-rs proof-sp proof-pq

Commutativity1Convertor {n = zero} (suc r) s p q proof-r proof-s proof-p proof-q proof-rs proof-sp proof-pq = ⊥.rec (!<0 (pred proof-r))

Commutativity1Convertor {n = suc n} (suc r) zero p q proof-r proof-s proof-p proof-q proof-rs proof-sp proof-pq = ⊥.rec (!<0 proof-rs)
Commutativity1Convertor {n = suc n} (suc r) (suc s) zero q proof-r proof-s proof-p proof-q proof-rs proof-sp proof-pq = ⊥.rec (!<0 proof-sp)
Commutativity1Convertor {n = suc n} (suc r) (suc s) (suc p) zero proof-r proof-s proof-p proof-q proof-rs proof-sp proof-pq = ⊥.rec (!<0 proof-pq)

Commutativity1Convertor {n = suc n} (suc r) (suc s) (suc p) (suc q) proof-r proof-s proof-p proof-q proof-rs proof-sp proof-pq i j = 
    addGen {n = n} (Commutativity1Convertor r s p q (pred proof-r) (pred proof-s) (pred proof-p) (pred proof-q) (pred proof-rs) (pred proof-sp) (pred proof-pq) i j)

---------------------------------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------------------------------



---------------------------------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------------------------------

Commutativity2Zero : {n : ℕ} → (r s q : ℕ) -- p- is short for proof-
                        → (p-p : 0 < (suc n)) → (p-r : r < (suc n)) → (p-s : s < (suc n)) → (p-q : q < (suc n)) -- proofs to make them fin suc n
                        → (p-pr : 0 < r) → (p-rs : r < s) → (p-sq : s < q) → (p-pq : 0 < q) → (p-rq : r < q)    -- condition for commutativity 2
                        → Square
                            (GenConvertor 0 q p-p p-q p-pq)
                            (GenConvertor 0 q p-p p-q p-pq)
                            (GenConvertor r s p-r p-s p-rs)
                            (GenConvertor r s p-r p-s p-rs)

Commutativity2Zero r s zero proof-p proof-r proof-s proof-q proof-pr proof-rs proof-sq proof-pq proof-rq i j =
    GenConvertor r s proof-r proof-s proof-rs i -- A p q does not exist so

Commutativity2Zero r s (suc zero) proof-p proof-r proof-s proof-q proof-pr proof-rs proof-sq proof-pq =  ⊥.rec (squeezeTheorem (trans proof-pr proof-rs) proof-sq)
Commutativity2Zero r s (suc (suc zero)) proof-p proof-r proof-s proof-q proof-pr proof-rs proof-sq proof-pq = ⊥.rec (squeezeTheorem2 proof-pr proof-rs proof-sq)
Commutativity2Zero zero s (suc (suc (suc zero))) proof-p proof-r proof-s proof-q proof-pr proof-rs proof-sq proof-pq = ⊥.rec (!<0 proof-pr)
Commutativity2Zero (suc r) zero (suc (suc (suc zero))) proof-p proof-r proof-s proof-q proof-pr proof-rs proof-sq proof-pq = ⊥.rec (!<0 proof-rs)
Commutativity2Zero (suc r) (suc zero) (suc (suc (suc zero))) proof-p proof-r proof-s proof-q proof-pr proof-rs proof-sq proof-pq = ⊥.rec (!<0 (pred proof-rs))

Commutativity2Zero (suc zero) (suc (suc zero)) (suc (suc (suc zero))) proof-p proof-r proof-s proof-q proof-pr proof-rs proof-sq proof-pq proof-rq i j =
     hcomp       (λ  { k ( i = i0) →  {!   !}
                      ; k ( i = i1) → {!   !}
                      ; k ( j = i0) → (Gen (1 , pred proof-s) ^ 2) {! i  !}
                      ; k ( j = i1) → (Gen (1 , pred proof-s) ^ 2) {! i  !}
                    }) 
     
     (((GenSwapper3 0 3 1 proof-p proof-q (pred proof-s) proof-pr proof-rq proof-pq) ∙v (GenSwapper3 0 3 1 proof-p proof-q (pred proof-s) proof-pr proof-rq proof-pq)) i j)
-- ((GenSwapper3 0 3 1 proof-p proof-q (pred proof-s) proof-pr proof-rq proof-pq) ∙v (GenSwapper3 0 3 1 proof-p proof-q (pred proof-s) proof-pr proof-rq proof-pq))

Commutativity2Zero (suc zero) (suc (suc (suc s))) (suc (suc (suc zero))) proof-p proof-r proof-s proof-q proof-pr proof-rs proof-sq proof-pq = {!   !}
Commutativity2Zero (suc (suc r)) (suc (suc s)) (suc (suc (suc zero))) proof-p proof-r proof-s proof-q proof-pr proof-rs proof-sq proof-pq = {!   !}

Commutativity2Zero r s (suc (suc (suc (suc q)))) proof-p proof-r proof-s proof-q proof-pr proof-rs proof-sq proof-pq i j = {!   !} 


Commutativity2Convertor : {n : ℕ} → (p r s q : ℕ) 
                        → (p-p : p < (suc n)) → (p-r : r < (suc n)) → (p-s : s < (suc n)) → (p-q : q < (suc n))   -- proofs to make them fin suc n
                        → (p-pr : p < r) → (p-rs : r < s) → (p-sq : s < q) → (p-pq : p < q) → (p-rq : r < q)       -- condition for commutativity 2
                        → Square
                            (GenConvertor p q p-p p-q p-pq)
                            (GenConvertor p q p-p p-q p-pq)
                            (GenConvertor r s p-r p-s p-rs)
                            (GenConvertor r s p-r p-s p-rs)

Commutativity2Convertor zero r s q proof-p proof-r proof-s proof-q proof-pr proof-rs proof-sq proof-pq proof-rq = 
    Commutativity2Zero r s q proof-p proof-r proof-s proof-q proof-pr proof-rs proof-sq proof-pq proof-rq

Commutativity2Convertor (suc p) zero s q proof-p proof-r proof-s proof-q proof-pr proof-rs proof-sq proof-pq proof-rq  = ⊥.rec (!<0 proof-pr)
Commutativity2Convertor (suc p) (suc r) zero q proof-p proof-r proof-s proof-q proof-pr proof-rs proof-sq proof-pq proof-rq  = ⊥.rec (!<0 proof-rs)
Commutativity2Convertor (suc p) (suc r) (suc s) zero proof-p proof-r proof-s proof-q proof-pr proof-rs proof-sq proof-pq proof-rq  = ⊥.rec (!<0 proof-sq)
Commutativity2Convertor {n = 0} (suc p) (suc r) (suc s) (suc q) proof-p proof-r proof-s proof-q proof-pr proof-rs proof-sq proof-pq proof-rq = ⊥.rec (!<0 (pred proof-q))

Commutativity2Convertor {n = suc n} (suc p) (suc r) (suc s) (suc q) proof-p proof-r proof-s proof-q proof-pr proof-rs proof-sq proof-pq proof-rq  i j =
    addGen {n = n} (Commutativity2Convertor 
        p r s q (pred proof-p) (pred proof-r) (pred proof-s) (pred proof-q) (pred proof-pr) (pred proof-rs) (pred proof-sq) (pred proof-pq) (pred proof-rq) i j) 


---------------------------------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------------------------------

-- A₁₃  = σ₂ σ₁² σ₂⁻¹   A₁₃ . A₄₅ =  σ₂ σ₁² σ₂⁻¹ . σ₄ σ₄
-- A₄₅  = σ₄ σ₄         A₄₅ . A₁₃ =  σ₄ σ₄ . σ₂ σ₁² σ₂⁻¹


-- A₀₃ = σ₂σ₁σ₀²σ₁⁻¹σ₂⁻¹
-- A₁₂ = σ₁²

-- PBraid≤Braid : {n : ℕ} (b : BPureBraid (suc n)) → Braid n
-- PBraid≤Braid base = base
-- PBraid≤Braid (gen p q proof-pq i) = GenConvertor (fst p) (fst q) (snd p) (snd q) proof-pq i
-- PBraid≤Braid (twoGencommutativity1 p q r s proof-rs proof-sp proof-pq i j) = 
--     Commutativity1Convertor (fst r) (fst s) (fst p) (fst q) (snd r) (snd s) (snd p) (snd q)  proof-rs proof-sp proof-pq i j

-- PBraid≤Braid (twoGencommutativity2 p q r s proof-pr proof-rs proof-sq proof-pq i j) = 
--     Commutativity2Convertor (fst p) (fst r) (fst s) (fst q) (snd p) (snd r) (snd s) (snd q) proof-pr proof-rs proof-sq proof-pq (trans proof-rs proof-sq) i j
    
-- PBraid≤Braid (threeGenCommutativityConnector r p q proof-rp proof-pq proof-rq i) = {!   !}
-- PBraid≤Braid (threeGenCommutativityLeft r p q proof-rp proof-pq proof-rq i j) = {!   !}
-- PBraid≤Braid (threeGenCommutativityMiddle r p q proof-rp proof-pq proof-rq i j) = {!   !}
-- PBraid≤Braid (threeGenCommutativityRight r p q proof-rp proof-pq proof-rq i j) = {!   !}
-- PBraid≤Braid (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq proof-rq proof-pq i) = {!   !}
-- PBraid≤Braid (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq proof-rq proof-pq i j) = {!   !}
-- PBraid≤Braid (fourGenCommutativity r p s q proof-rp proof-ps proof-sq proof-rs proof-rq proof-pq i j) = {!   !}
 
   
   