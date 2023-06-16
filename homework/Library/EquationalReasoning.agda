module homework.Library.EquationalReasoning where

open import Cubical.Core.Primitives

open import homework.2--Paths-and-Identifications.2-1--Paths
open import homework.2--Paths-and-Identifications.2-4--Composition-and-Filling

private
  variable
    ℓ ℓ' : Level
    A B : Type ℓ
    x y z w : A

infix  3 _∎
infixr 2 step-≡ _≡⟨⟩_
infixr 2.5 _≡⟨_⟩≡⟨_⟩_

-- Syntax for chains of equational reasoning

step-≡ : (x : A) → y ≡ z → x ≡ y → x ≡ z
step-≡ _ p q = q ∙ p

syntax step-≡ x y p = x ≡⟨ p ⟩ y

≡⟨⟩-syntax : (x : A) → y ≡ z → x ≡ y → x ≡ z
≡⟨⟩-syntax = step-≡

infixr 2 ≡⟨⟩-syntax
syntax ≡⟨⟩-syntax x y (λ i → B) = x ≡[ i ]⟨ B ⟩ y

_≡⟨⟩_ : (x : A) → x ≡ y → x ≡ y
_ ≡⟨⟩ x≡y = x≡y

≡⟨⟩⟨⟩-syntax : (x y : A) → x ≡ y → y ≡ z → z ≡ w → x ≡ w
≡⟨⟩⟨⟩-syntax x y p q r = p ∙∙ q ∙∙ r
infixr 3 ≡⟨⟩⟨⟩-syntax
syntax ≡⟨⟩⟨⟩-syntax x y B C = x ≡⟨ B ⟩≡ y ≡⟨ C ⟩≡

_≡⟨_⟩≡⟨_⟩_ : (x : A) → x ≡ y → y ≡ z → z ≡ w → x ≡ w
_ ≡⟨ x≡y ⟩≡⟨ y≡z ⟩ z≡w = x≡y ∙∙ y≡z ∙∙ z≡w

_∎ : (x : A) → x ≡ x
_ ∎ = refl
