{-# OPTIONS --safe #-}


module Braid.BraidGroup where

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude 
open import Cubical.Data.Nat.Base hiding (_·_)
open import Cubical.Data.Fin.Base 
open import Cubical.Data.Nat.Order renaming (suc-≤-suc to sucP)
open import Cubical.Data.Int hiding (_+_ ; _·_)
open import Cubical.Data.Sigma



-- Braid group with n generators, so n + 1 strands
data Braid (n : ℕ) : Type where 

    base : Braid n -- base point for loops
    gen : (i : Fin n) → base ≡ base
    

    {-
    σᵢ is the ith generator
    Commutativity : σᵢσ­ⱼ = σ­ⱼσᵢ   0 ≤ i,j ≤ n - 1 ;  |i - j| ≥ 2 <=> |i - j| > 1
      
                   σⱼ
               b - - - > b
               ^         ^
          σᵢ   |         |  σᵢ                       ^
               |         |                         j |
               b — — — > b                           ∙ — >
                  σⱼ                                   i

    -}
    commutativity1 : (p q : Fin n) → (proof-pq : suc (toℕ p) < (toℕ q) ) → Square (gen p) (gen p) (gen q) (gen q)      
    commutativity2 : (p q : Fin n) → (proof-qp : suc (toℕ q) < (toℕ p) ) → Square (gen p) (gen p) (gen q) (gen q)      
    


    {-
    Pull Through  : σᵢ σᵢ₊₁ σᵢ = σᵢ₊₁ σᵢ σᵢ₊₁  for 0 ≤ i ≤ n-2
    
                  σᵢ₊₁
               b - - - > b
               ^         ^
          σ­ᵢ   |         |   σ­ᵢ                
               |         |                        
               b — — — > b  pullThroughMid                    
               ^         ^
               |         |
        σᵢ₊₁   |         |   σᵢ₊₁
               b - - - > b
                   σ­ᵢ
                                                 
    -}
    -- p means k ≤ n - 2
    pullThroughMid : (k : Fin n ) → (constraint : (toℕ k + 1) < n ) → base ≡ base
    pullThroughTop : (k : Fin n) → (constraint : (toℕ k + 1) < n ) → Square (gen k) (gen k) (pullThroughMid k constraint) (gen (toℕ k + 1 , constraint))
    pullThroughBottom : (k : Fin n) → (constraint : (toℕ k + 1) < n ) → Square (gen (toℕ k + 1 , constraint)) (gen (toℕ k + 1 , constraint))  (gen k) (pullThroughMid k constraint)


addGen : {n : ℕ} (b : Braid n) → Braid (suc n)
addGen base = base
addGen (gen p i) = gen (fsuc p) i -- add generator to zero-th position and shift up
addGen (commutativity1 p q proof-pq i j) =  commutativity1 (fsuc p) (fsuc q) (sucP proof-pq) i j
addGen (commutativity2 p q proof-qp i j) =  commutativity2 (fsuc p) (fsuc q) (sucP proof-qp) i j 

addGen (pullThroughMid k constraint i) =  pullThroughMid (fsuc k) (sucP constraint) i 
addGen (pullThroughTop k proof i j) =  pullThroughTop (fsuc k) (sucP proof) i j 
addGen (pullThroughBottom k proof i j) =  pullThroughBottom (fsuc k) (sucP proof) i j 





{-
-- Deletion operation does not work as pullThrough fails.
We get a square which is :

                  σᵢ₊₁
               b - - - > b
               ^         ^
          refl |         |   σ­ᵢ                
               |         |                        
               b — — — > b  pullThroughMid σ₀   σ₀ = σ₀ · σ₀                     
               ^         ^
               |         |
       σ₀      |         |   σ₀
               b - - - > b
                   refl

Which gives us the path  σ₀ ≡ σ₀ · σ₀ , a contradiction!!

delGen : {n : ℕ} (b : Braid (suc n) ) → Braid n
delGen base = base
delGen (gen (zero , proof) i) = base
delGen (gen (suc m , proof) i) = gen (m , pred-≤-pred proof) i


delGen (commutativity (zero , proof-m) (zero , proof-n) constraint i j) = base
delGen (commutativity (zero , proof-m) (suc n , proof-n) constraint i j) = gen (n , pred-≤-pred proof-n) i
delGen (commutativity (suc m , proof-m) (zero , proof-n) constraint i j) = gen (m , pred-≤-pred proof-m) j
delGen (commutativity (suc m , proof-m) (suc n , proof-n) constraint i j) = commutativity (m , pred-≤-pred proof-m) (n , pred-≤-pred proof-n) constraint i j


delGen (pullThroughMid (zero , proof) constraint i) = gen (zero , pred-≤-pred constraint) i
delGen (pullThroughMid (suc m , proof) constraint i) = pullThroughMid (m , pred-≤-pred proof) (pred-≤-pred constraint) i

delGen (pullThroughTop (zero , proof) constraint i j) = gen (zero , pred-≤-pred constraint) i
delGen (pullThroughTop (suc m , proof) constraint i j) = pullThroughTop (m , pred-≤-pred proof) (pred-≤-pred constraint) i j

delGen (pullThroughBottom (zero , proof) constraint i j) =  gen (zero , pred-≤-pred constraint) {! j  !}
delGen (pullThroughBottom (suc m , proof) constraint i j) = pullThroughBottom (m , pred-≤-pred proof) (pred-≤-pred constraint) i j  

-}




 