{-# OPTIONS --safe #-}


module homework.braid.BraidGroup where

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude 
open import Cubical.Foundations.Path
open import Cubical.Data.Nat.Base hiding (_·_)
open import Cubical.Data.Fin.Base 
open import Cubical.Data.Nat.Order 
open import Cubical.Data.Bool hiding (_≤_)
open import Cubical.Data.Int hiding (_+_ ; _·_)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat.Order.Recursive using () renaming (_≤_ to _≤′_)



private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Type ℓ
    B : A → Type ℓ
    x y z w : A

∂ : I → I
∂ i = i ∨ ~ i

-- -- Braid group with n generators, so n + 1 strands
-- data Braid (n : ℕ) : Type where 

--     base : Braid n -- base point for loops
--     gen : (i : Fin n) → base ≡ base

--     {-
--     σᵢ is the ith generator
--     Commutativity : σᵢσ­ⱼ = σ­ⱼσᵢ   0 ≤ i , j ≤ n - 1 ;  |i - j| ≥ 2 <=> |i - j| > 1
      
--                    σⱼ
--                b - - - > b
--                ^         ^
--           σᵢ   |         |  σᵢ                       ^
--                |         |                         j |
--                b — — — > b                           ∙ — >
--                   σⱼ                                   i

--     -}
--     commutativity : (i j : Fin n) → (abs (fst i ℕ- fst j) > 1) → Square (gen i) (gen i) (gen j) (gen j)           
    

--     {-
--     Pull Through  : σᵢ σᵢ₊₁ σᵢ = σᵢ₊₁ σᵢ σᵢ₊₁  for 0 ≤ i ≤ n-2
    
--                  σᵢ₊₁ σᵢ
--                b - - - > b
--                ^         ^
--           σᵢ   |         |   σᵢ σᵢ₊₁                 ^
--                |         |                         j |
--                b — — — > b                           ∙ — >
--                   σᵢ₊₁                                 i

--     -}
--     pullThrough : (k : Fin n) → (p : (toℕ k + 1) < n ) → Square (gen k)
--                                                                 ((gen k) ∙ gen (toℕ k + 1 , p))
--                                                                 (gen (toℕ k + 1 , p))
--                                                                 (gen (toℕ k + 1 , p) ∙ (gen k )) 





-- addGen : {n : ℕ} (b : Braid n) → Braid (suc n)
-- addGen base = base
-- addGen (gen (m , proof) i) = gen (m , ≤-suc proof ) i
-- addGen (commutativity p q constraint i j) = commutativity (toℕ p , ≤-suc (snd p)) (toℕ q , ≤-suc (snd q)) constraint i j
-- addGen (pullThrough k proof i j) = pullThrough {!   !} {!   !}  i {! j  !}
-- -- addGen (pullThrough k proof i j) = pullThrough (toℕ k , ≤-suc (snd k)) (≤-suc proof)  i  {! j  !}


-- reduce : {n : ℕ} (b : Braid (suc n) ) → Braid n
-- reduce base = base
-- reduce (gen (zero , proof) i) = base
-- reduce (gen (suc m , proof) i) = gen (m , pred-≤-pred proof) i
-- reduce (commutativity p q constraint i j) = {!   !}
-- reduce (pullThrough n p i j) = {!   !}

{-
                                  gen (fst q , ≤-suc (snd q)) i
                                b - - - > b
                                ^         ^
gen (fst p , ≤-suc (snd p)) j   |         |   gen (fst p , ≤-suc (snd p)) j                      ^
                                |         |                                                    j |
                                b — — — > b                                                      ∙ — >
                                     gen (fst q , ≤-suc (snd q)) i                                 i


-}
-- Pure braid group  



-- Braid group with n generators, so n + 1 strands
data Braid (n : ℕ) : Type where 

    base : Braid n -- base point for loops
    gen : (i : Fin n) → base ≡ base
    

    {-
    σᵢ is the ith generator
    Commutativity : σᵢσ­ⱼ = σ­ⱼσᵢ   0 ≤ i , j ≤ n - 1 ;  |i - j| ≥ 2 <=> |i - j| > 1
      
                   σⱼ
               b - - - > b
               ^         ^
          σᵢ   |         |  σᵢ                       ^
               |         |                         j |
               b — — — > b                           ∙ — >
                  σⱼ                                   i

    -}
    commutativity : (i j : Fin n) → (abs (fst i ℕ- fst j) > 1) → Square (gen i) (gen i) (gen j) (gen j)      
    


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
addGen (gen (m , proof) i) = gen (m , ≤-suc proof) i
addGen (commutativity p q constraint i j) = commutativity (toℕ p , ≤-suc (snd p)) (toℕ q , ≤-suc (snd q)) constraint i j
addGen (pullThroughMid k constraint i) = pullThroughMid (toℕ k , ≤-suc (snd k)) (≤-suc constraint) i
addGen (pullThroughTop k proof i j) = pullThroughTop ( toℕ k , ≤-suc (snd k)) (≤-suc proof) i j
addGen (pullThroughBottom k proof i j) = pullThroughBottom ( toℕ k , ≤-suc (snd k)) (≤-suc proof) i j





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

Which gives us the path  σ₀ ≡ σ₀ · σ₀ , a contradiction!!

-}

reduce : {n : ℕ} (b : Braid (suc n) ) → Braid n
reduce base = base
reduce (gen (zero , proof) i) = base
reduce (gen (suc m , proof) i) = gen (m , pred-≤-pred proof) i


reduce (commutativity (zero , proof-m) (zero , proof-n) constraint i j) = base
reduce (commutativity (zero , proof-m) (suc n , proof-n) constraint i j) = gen (n , pred-≤-pred proof-n) i
reduce (commutativity (suc m , proof-m) (zero , proof-n) constraint i j) = gen (m , pred-≤-pred proof-m) j
reduce (commutativity (suc m , proof-m) (suc n , proof-n) constraint i j) = commutativity (m , pred-≤-pred proof-m) (n , pred-≤-pred proof-n) constraint i j


reduce (pullThroughMid (zero , proof) constraint i) = gen (zero , pred-≤-pred constraint) i
reduce (pullThroughMid (suc m , proof) constraint i) = pullThroughMid (m , pred-≤-pred proof) (pred-≤-pred constraint) i

reduce (pullThroughTop (zero , proof) constraint i j) = gen (zero , pred-≤-pred constraint) i
reduce (pullThroughTop (suc m , proof) constraint i j) = pullThroughTop (m , pred-≤-pred proof) (pred-≤-pred constraint) i j

reduce (pullThroughBottom (zero , proof) constraint i j) =  gen (zero , pred-≤-pred constraint) {! j  !}
reduce (pullThroughBottom (suc m , proof) constraint i j) = pullThroughBottom (m , pred-≤-pred proof) (pred-≤-pred constraint) i j  





 