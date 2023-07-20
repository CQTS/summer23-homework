{-# OPTIONS --safe #-}
module Braid.Permutation.Iso where


open import Cubical.Foundations.Prelude
-- open import
open import Cubical.Data.Nat
open import Cubical.Data.Fin
open import Braid.PureBraid
open import Cubical.Algebra.Group
open import Cubical.Algebra.SymmetricGroup



PBraid→Symmetric : (n : ℕ) → (b : BPureBraid n) → fst (Sym n)
PBraid→Symmetric n b = {! Sym n !}


Symmetric→PBraid : (n : ℕ) → (s : fst (Sym n)) → BPureBraid n
Symmetric→PBraid n (fst₁ , snd₁) = {! snd₁  !}



 