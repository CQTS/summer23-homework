module homework.conf.conf where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.HITs.Bouquet
open import Cubical.Data.Nat
open import Cubical.Data.Empty
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Sum

Fin : ℕ → Type
Fin 0 = ⊥
Fin (suc n) = ⊤ ⊎ (Fin n)

∂Path : (n : ℕ) → base {A = Fin n} ≡ base
∂Path n = {!   !}

Circle : Type
Circle = Bouquet ⊤

Circle-rec : ∀ {ℓ} {A : Type ℓ} (a : A) (p : a ≡ a)
            → Circle → A
Circle-rec a p base = a
Circle-rec a p (loop _ i) = p i

ConfStruct : ℕ → Type → Type
ConfStruct n X = Σ[ b ∈ X ] (Σ[ gen ∈ (( i : Fin n ) → Circle → X) ] (b ≡ b))

standardConf : (n : ℕ) → TypeWithStr ℓ-zero (ConfStruct n)
standardConf n = (Bouquet (Fin n) , base , (λ k  → Circle-rec base (loop k)) , ∂Path n)


{-
Two main tasks:

1. Use SIP to show that standardConf n ≡ standardConf n is equivalent to the group of automorphisms of FreeGroup (Fin n) which send each generator to a conjugate
of itself and which preserve the product of all generators

2. Define the pure braid group in terms of generators and relations, and show that it is equivalent to the subgroup of the Aut (FreeGroup (Fin n)) which send each
generator to a conjugate of itself and which preserve the product of all generators

ϕ g = (w g) · g (w g) ⁻¹
w L Fin n → FreeGroup (Fin n)

toHom : (A → FreeGroup A) → HomGroup (FreeGroup A , FreeGroup A)
-}