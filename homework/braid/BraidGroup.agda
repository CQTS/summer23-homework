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
    
                 σᵢ₊₁ σᵢ
               b - - - > b
               ^         ^
          σᵢ   |         |   σᵢ σᵢ₊₁                 ^
               |         |                         j |
               b — — — > b                           ∙ — >
                  σᵢ₊₁                                 i

    -}
    pullThrough : (k : Fin n) → (p : (toℕ k + 1) < n ) → Square (gen k)
                                                                ((gen k) ∙ gen (toℕ k + 1 , p))
                                                                (gen (toℕ k + 1 , p))
                                                                (gen (toℕ k + 1 , p) ∙ (gen k )) 

{-


       
      

                                                        r : σᵢ  p : σᵢ₊₁ r p r = p r p
                              refl
                      b - - - - - - - - > b
                    / ^                 / ^
     (σᵢ σᵢ₊₁ σᵢ) /   |               /  (σᵢ₊₁ σᵢ σᵢ₊₁)
                /     |             /     |
              b - - - - - - - - - > b     |
              ^       |           ^       | σᵢ₊₁               ^   j
              |     σᵢ₊₁ σ₁       |       |                  k | /
              |       |           |       |                    ∙ — >
              |       |    refl   |       |                      i
              |       b - - - - - | - - > b
             refl   /             |     /
              |   /  σᵢ           |   /   σᵢ₊₁ σᵢ
              | /                 | /
              b - - - - - - - - > b
                      refl

-}


reduce : {n : ℕ} (b : Braid (suc n)) → Braid n
reduce b = {!   !}