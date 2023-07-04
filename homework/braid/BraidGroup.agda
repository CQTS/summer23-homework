{-# OPTIONS --safe #-}


module homework.braid.BraidGroup where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat.Base
open import Cubical.Data.Fin.Base


data Braid : {n : ℕ} → Type where
    base : Braid


