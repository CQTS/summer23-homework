module homework-solutions.Library.Univalence where

open import Cubical.Core.Primitives public
open import Cubical.Core.Glue public
open import Cubical.Foundations.Prelude using (cong)
open import Cubical.Foundations.Function using (_∘_)

open import homework-solutions.1--Type-Theory.1-2--Inductive-Types
open import homework-solutions.1--Type-Theory.1-1--Types-and-Functions hiding (_∘_)
open import homework-solutions.2--Paths-and-Identifications.2-1--Paths hiding (cong)
open import homework-solutions.2--Paths-and-Identifications.2-2--Path-Algebra-and-J
open import homework-solutions.2--Paths-and-Identifications.2-4--Composition-and-Filling

private
  variable
    ℓ ℓ' : Level
    A B C : Type ℓ

isContr : ∀ {ℓ} → Type ℓ → Type ℓ
isContr A = Σ A \ x → (∀ y → x ≡ y)

isContr⊤ : isContr ⊤
isContr⊤ = tt , λ {tt → refl}

fiber : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) (y : B) → Type (ℓ-max ℓ ℓ')
fiber {A = A} f y = Σ[ x ∈ A ] f x ≡ y

-- Helper function for constructing equivalences from pairs (f,g) that cancel each other up to definitional
-- equality. For such (f,g), the result type simplifies to isContr (fiber f b).
strictContrFibers : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {f : A → B} (g : B → A) (b : B)
  → Σ[ t ∈ fiber f (f (g b)) ]
    ((t' : fiber f b) → Path (fiber f (f (g b))) t (g (f (t' .fst)) , cong (f ∘ g) (t' .snd)))
strictContrFibers {f = f} g b .fst = (g b , refl)
strictContrFibers {f = f} g b .snd (a , p) i = (g (p (~ i)) , λ j → f (g (p (~ i ∨ j))))

-- The identity equivalence
idfun : (A : Type ℓ) → A → A
idfun _ x = x

idIsEquiv : ∀ {ℓ} (A : Type ℓ) → isEquiv (idfun A)
idIsEquiv A .equiv-proof = strictContrFibers (idfun A)

idEquiv : ∀ {ℓ} (A : Type ℓ) → A ≃ A
idEquiv A .fst = idfun A
idEquiv A .snd = idIsEquiv A

-- Any iso is an equivalence
module _ (i : Iso A B) where
  open Iso i renaming ( fun to f
                      ; inv to g
                      ; rightInv to s
                      ; leftInv to t)

  private
    module _ (y : B) (x0 x1 : A) (p0 : f x0 ≡ y) (p1 : f x1 ≡ y) where
      fill0 : I → I → A
      fill0 i = hfill (λ k → λ { (i = i1) → t x0 k
                               ; (i = i0) → g y })
                      (inS (g (p0 (~ i))))

      fill1 : I → I → A
      fill1 i = hfill (λ k → λ { (i = i1) → t x1 k
                               ; (i = i0) → g y })
                      (inS (g (p1 (~ i))))

      fill2 : I → I → A
      fill2 i = hfill (λ k → λ { (i = i1) → fill1 k i1
                               ; (i = i0) → fill0 k i1 })
                      (inS (g y))

      p : x0 ≡ x1
      p i = fill2 i i1

      sq : I → I → A
      sq i j = hcomp (λ k → λ { (i = i1) → fill1 j (~ k)
                              ; (i = i0) → fill0 j (~ k)
                              ; (j = i1) → t (fill2 i i1) (~ k)
                              ; (j = i0) → g y })
                     (fill2 i j)

      sq1 : I → I → B
      sq1 i j = hcomp (λ k → λ { (i = i1) → s (p1 (~ j)) k
                               ; (i = i0) → s (p0 (~ j)) k
                               ; (j = i1) → s (f (p i)) k
                               ; (j = i0) → s y k })
                      (f (sq i j))

      lemIso : (x0 , p0) ≡ (x1 , p1)
      lemIso i .fst = p i
      lemIso i .snd = λ j → sq1 i (~ j)

  isoToIsEquiv : isEquiv f
  isoToIsEquiv .equiv-proof y .fst .fst = g y
  isoToIsEquiv .equiv-proof y .fst .snd = s y
  isoToIsEquiv .equiv-proof y .snd z = lemIso y (g y) (fst z) (s y) (snd z)


isoToEquiv : Iso A B → A ≃ B
isoToEquiv i .fst = i .Iso.fun
isoToEquiv i .snd = isoToIsEquiv i

equivToIso : {A : Type ℓ} {B : Type ℓ'} → A ≃ B → Iso A B
equivToIso e = iso (fst e) (inv e) (s e) (r e)
  where
    inv : {A : Type ℓ} {B : Type ℓ'} → A ≃ B → B → A
    inv e b = fst (fst (equiv-proof (snd e) b))

    s : (e : A ≃ B) → section (fst e) (inv e)
    s (e , is-equiv) y = is-equiv .equiv-proof y .fst .snd

    r : (e : A ≃ B) → retract (fst e) (inv e)
    r (e , is-equiv) x i = is-equiv .equiv-proof (e x) .snd (x , refl) i .fst

isoToPath : Iso A B → A ≡ B
isoToPath {A = A} {B = B} f i =
  Glue B (λ { (i = i0) → (A , isoToEquiv f)
            ; (i = i1) → (B , idEquiv B) })
