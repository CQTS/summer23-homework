{-# OPTIONS --safe #-}
module Braid.Isomorphism.function where

open import Cubical.Foundations.Prelude

open import Braid.PureBraidReducedConstraints
open import Braid.PureBraid
open import Cubical.Data.Nat.Order renaming (pred-≤-pred to pred ; <-weaken to weaken; <-asym to asym ; <-trans to trans ; <→≢ to <!=)
open import Cubical.Data.Nat
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Fin


BPureBraid→BPureBraid' : ∀ n → (b : BPureBraid n) → BPureBraid' n
BPureBraid→BPureBraid' n base = base
BPureBraid→BPureBraid' n (gen p q i) = gen p q i
BPureBraid→BPureBraid' n (identity p i j) = identity p i j
BPureBraid→BPureBraid' n (genEquality p q i j) = genEquality p q i j
BPureBraid→BPureBraid' n (twoGenCommutativity1 p q r s proof-rp proof-sp proof-rq proof-sq i j) = twoGenCommutativity1 p q r s proof-rp proof-sp proof-rq proof-sq i j
BPureBraid→BPureBraid' n (twoGenCommutativity2 p q r s proof-pr proof-ps proof-rq proof-sq i j) = twoGenCommutativity2 p q r s proof-pr proof-ps proof-rq proof-sq i j
BPureBraid→BPureBraid' n (threeGenCommutativityConnector r p q i) = threeGenCommutativityConnector r p q i 
BPureBraid→BPureBraid' n (threeGenCommutativityComposition r p q i j) = threeGenCommutativityLeft r p q i j
BPureBraid→BPureBraid' n (threeGenCommutativity r p q i j)  = hcomp (λ { k ( i = i0)    →   threeGenCommutativityLeft r p q j (~ k)
                                                                      ; k ( i = i1)    →    threeGenCommutativityRight q r p j (~ k)
                                                                      ; k ( j = i0)    →     genEquality p q i (~ k)
                                                                      ; k ( j = i1)    →     genEquality r q i k}) 
                                                                      (gen r p j)


--                                                                
--                                                       b - - - - - - - - > b
--                          threegenconn r p q        /  ^                 / ^     threegenconn q r p
--                                                  /    |  Arq          /   |
--                                                /      |             /     |
--                                               b - - - - - - - - > b       |
--                                               ^       |           ^       |  A q r             ^  j
--                                               |       |           |       |                  k | /
--                                          sym  |       |           | sym   |                    ∙ — >
--                                          Apq  |       |           | Aqp   |                      i
--                                               |       b - - - - - | - - > b
--                                               |     /             |     /
--                                               |   / A r p         |   /  A r p 
--                                               | /                 | /
--                                               b - - - - - - - - > b
--                                                       

                                                                          --  Right connector
    --                              A r p                                     A r p
    --                          b - - - > b                                b - - - > b         
    --                          ^         ^                                ^         ^
    --                    A p q |         | sym (A r q)             A q p  |         |  sym (A q r)
    --                          |         |                                |         |
    --                          b — — — > b                                b - - - > b
    --                            conn r p q                                 conn q r p


BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) = fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i
BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) = fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j
BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) = fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j