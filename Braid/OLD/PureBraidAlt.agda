{-# OPTIONS --safe #-}


module Braid.OLD.PureBraidAlt where
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat.Base
open import Cubical.Data.Fin.Base
open import Cubical.Data.Nat.Order renaming (pred-≤-pred to pred ; suc-≤-suc to sucP)
open import Cubical.Data.Empty as ⊥
-- open import homework.2--Paths-and-Identifications.2-4--Composition-and-Filling using (doubleCompPath-filler')



-- data B3 : Type where
--   base  : B3
--   generator1 : base ≡ base
--   generator2 : base ≡ base
--   relation : Square generator1 generator1 generator2 generator2
--   makeGroupoid : {x y : B3} → isSet (x ≡ y)





data BPureBraid' (n : ℕ) :  Type where -- the space whose loops are the pure braid group of n strands
  base : BPureBraid' n
  gen  : (p q : Fin n) → (constraint : toℕ p < toℕ q)  → base ≡ base

  -- genRule : (p q : Fin n) → (toℕ p < toℕ q) →

  twoGenCommutativity1 : (p q r s : Fin n) → (proof-rs : toℕ r < toℕ s)
                          → ( proof-sp : toℕ s < toℕ p)
                          → ( proof-pq : toℕ p < toℕ q)
                          →  Square (gen p q proof-pq)  (gen p q proof-pq) (gen r s proof-rs ) (gen r s proof-rs)

  twoGenCommutativity2 : (p q r s : Fin n) → (proof-pr : toℕ p < toℕ r)
                          → ( proof-rs : toℕ r < toℕ s)
                          → ( proof-sq : toℕ s < toℕ q)
                          → ( proof-pq : toℕ p < toℕ q) -- redundant

                          →  Square (gen p q proof-pq)  (gen p q proof-pq) (gen r s proof-rs) (gen r s proof-rs)




--               A r q                             A r q                              sym (A r p)
--             b - - - > b                       b - - - > b                         b - - - > b
--            ^         ^                       ^         ^                          ^         ^
--     A r p  |         |  3GenCommon    A r p  |         |              3GenCommon  |         |  A p q
--            |         |                       |         |  sym (A p q)             |         |
--            b — — — > b                       b — — — > b                          b — — — > b
--             sym (A p q)                       3GenCommon                             A r q

  threeGenCommutativityConnector : (r p q : Fin n) → (proof-rp : toℕ r < toℕ p) → (proof-pq : toℕ p < toℕ q) → (proof-rq : toℕ r < toℕ q) → base ≡ base

  threeGenCommutativityLeft : (r p q : Fin n) → (proof-rp : toℕ r < toℕ p) → (proof-pq : toℕ p < toℕ q) → (proof-rq : toℕ r < toℕ q) → Square
                                                                                                                                        (gen p q proof-pq)
                                                                                                                                        (sym (gen r q proof-rq))
                                                                                                                                        (threeGenCommutativityConnector r p q proof-rp proof-pq proof-rq)
                                                                                                                                        (gen r p proof-rp )

  threeGenCommutativityMiddle : (r p q : Fin n) → (proof-rp : toℕ r < toℕ p) → (proof-pq : toℕ p < toℕ q) → (proof-rq : toℕ r < toℕ q) → Square
                                                                                                                                        (gen r p proof-rp)
                                                                                                                                        (sym (gen p q proof-pq))
                                                                                                                                        (threeGenCommutativityConnector r p q proof-rp proof-pq proof-rq)
                                                                                                                                        (gen r q proof-rq)

                                                                                                                                      
  threeGenCommutativityRight : (r p q : Fin n) → (proof-rp : toℕ r < toℕ p) → (proof-pq : toℕ p < toℕ q) → (proof-rq : toℕ r < toℕ q) → Square
                                                                                                                                        (gen r q proof-rq)
                                                                                                                                        (sym (gen r p proof-rp))
                                                                                                                                        (threeGenCommutativityConnector r p q proof-rp proof-pq proof-rq)
                                                                                                                                        (gen p q proof-pq)



  fourGenCommutativityConnector : (r p s q : Fin n) → (proof-rp : toℕ r < toℕ p) → (proof-ps : toℕ p < toℕ s) → (proof-sq : toℕ s < toℕ q) → (proof-rq : toℕ r < toℕ q) → (proof-pq : toℕ p < toℕ q) → base ≡ base

      --           A p q
      --        b ­- - - > b
      --        ^         ^
      --   A r q|         |  sym (A s q)
      --        |         |
      --        b - - - > b
      --            Conn

  fourGenCommutativityComposition : (r p s q : Fin n) → (proof-rp : toℕ r < toℕ p) → (proof-ps : toℕ p < toℕ s) → (proof-sq : toℕ s < toℕ q) → (proof-rq : toℕ r < toℕ q) → (proof-pq : toℕ p < toℕ q) → Square
                                                                                                                                                                                                            (gen r q proof-rq)
                                                                                                                                                                                                            (sym (gen s q proof-sq))
                                                                                                                                                                                                            (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq proof-rq proof-pq )
                                                                                                                                                                                                            (gen p q proof-pq)

  fourGenCommutativity : (r p s q : Fin n) → (proof-rp : toℕ r < toℕ p) → (proof-ps : toℕ p < toℕ s) → (proof-sq : toℕ s < toℕ q) → (proof-rs : toℕ r < toℕ s) → (proof-rq : toℕ r < toℕ q) → (proof-pq : toℕ p < toℕ q) → Square
                                                                                                                                                                                                                              (gen r s proof-rs)
                                                                                                                                                                                                                              (gen r s proof-rs)
                                                                                                                                                                                                                              (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq proof-rq proof-pq)
                                                                                                                                                                                                                              (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq proof-rq proof-pq)






addGen : {n : ℕ} (b : BPureBraid' n) → BPureBraid' (suc n)
addGen base = base
addGen (gen (m , proof-m) (n , proof-n) constraint i) = gen (m , ≤-suc proof-m) (n , ≤-suc proof-n) constraint i
addGen (twoGenCommutativity1 (p , proof-p) (q , proof-q) (r , proof-r) (s , proof-s) proof-rs proof-sp proof-pq i j) = twoGenCommutativity1 (p , ≤-suc proof-p) (q , ≤-suc proof-q) (r , ≤-suc proof-r) (s , ≤-suc proof-s) proof-rs proof-sp proof-pq i j
addGen (twoGenCommutativity2 (p , proof-p) (q , proof-q) (r , proof-r) (s , proof-s) proof-pr proof-rs proof-sq proof-pq i j) = twoGenCommutativity2 (p , ≤-suc proof-p ) ( q , ≤-suc proof-q) (r , ≤-suc proof-r) (s , ≤-suc proof-s) proof-pr  proof-rs proof-sq proof-pq i j


addGen (threeGenCommutativityConnector (r , proof-r) (p , proof-p) (q , proof-q) proof-rp proof-pq proof-rq i)  = threeGenCommutativityConnector ( r , ≤-suc proof-r) (p , ≤-suc proof-p) (q , ≤-suc proof-q) proof-rp proof-pq proof-rq i
addGen (threeGenCommutativityLeft (r , proof-r) (p , proof-p) (q , proof-q)  proof-rp proof-pq proof-rq i j) = threeGenCommutativityLeft (r , ≤-suc proof-r) (p , ≤-suc proof-p) (q , ≤-suc proof-q) proof-rp proof-pq proof-rq i j
addGen (threeGenCommutativityMiddle (r , proof-r) (p , proof-p) (q , proof-q) proof-rp proof-pq proof-rq i j) = threeGenCommutativityMiddle (r , ≤-suc proof-r) (p , ≤-suc proof-p) (q , ≤-suc proof-q) proof-rp proof-pq proof-rq i j
addGen (threeGenCommutativityRight (r , proof-r) (p , proof-p) (q , proof-q)  proof-rp proof-pq proof-rq i j)  =  threeGenCommutativityRight (r , ≤-suc proof-r) (p , ≤-suc proof-p) (q , ≤-suc proof-q) proof-rp proof-pq proof-rq i j

addGen (fourGenCommutativityComposition (r , proof-r) (p , proof-p) (s , proof-s) (q , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i j) = fourGenCommutativityComposition (r , ≤-suc proof-r) (p , ≤-suc proof-p) (s , ≤-suc proof-s) (q , ≤-suc proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i j
addGen (fourGenCommutativity (r , proof-r) (p , proof-p) (s , proof-s) (q , proof-q) proof-rp proof-ps proof-sq proof-rs proof-rq proof-pq i j) = fourGenCommutativity (r , ≤-suc proof-r) (p , ≤-suc proof-p) (s , ≤-suc proof-s) (q , ≤-suc proof-q) proof-rp proof-ps proof-sq proof-rs proof-rq proof-pq i j
addGen (fourGenCommutativityConnector (r , proof-r) (p , proof-p) (s , proof-s) (q , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i ) = fourGenCommutativityConnector (r , ≤-suc proof-r) (p , ≤-suc proof-p) (s , ≤-suc proof-s) (q , ≤-suc proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i



deletion : {n : ℕ} (b : BPureBraid' (suc n)) → BPureBraid' n
deletion base = base

deletion (gen (zero , proof-p) (q , proof-q) constraint i) = base
deletion (gen (suc p , proof-p) (zero , proof-q) constraint i) = base
deletion (gen (suc p , proof-p) (suc q , proof-q) constraint i) = gen ( p , pred proof-p) (q , pred proof-q) (pred constraint) i


-- Commutivity case 1 : r < s < p < q  ⇒ (gen p q ) · (gen r s) ≡ (gen r s) ∙ (gen p q)
-- these cases are absurd and will not be used
deletion (twoGenCommutativity1 (zero , proof-p) (zero , proof-q) (zero , proof-r) (zero , proof-s) proof-rs proof-sp proof-pq i j) = base
deletion (twoGenCommutativity1 (zero , proof-p) (zero , proof-q) (zero , proof-r) (suc s , proof-s) proof-rs proof-sp proof-pq i j) = base
deletion (twoGenCommutativity1 (zero , proof-p) (zero , proof-q) (suc r , proof-r) (zero , proof-s) proof-rs proof-sp proof-pq i j) =  base
deletion (twoGenCommutativity1 (suc p , proof-p) (zero , proof-q) (zero , proof-r) (zero , proof-s) proof-rs proof-sp proof-pq i j) =  base
deletion (twoGenCommutativity1 (suc p , proof-p) (zero , proof-q) (zero , proof-r) (suc s , proof-s) proof-rs proof-sp proof-pq i j) = base
deletion (twoGenCommutativity1 (suc p , proof-p) (zero , proof-q) (suc r , proof-r) (zero , proof-s) proof-rs proof-sp proof-pq i j) = base
deletion (twoGenCommutativity1 (zero , proof-p) (suc q , proof-q) (zero , proof-r) (zero , proof-s) proof-rs proof-sp proof-pq i j) = base
deletion (twoGenCommutativity1 (zero , proof-p) (suc q , proof-q) (zero , proof-r) (suc s , proof-s) proof-rs proof-sp proof-pq i j) = base
deletion (twoGenCommutativity1 (zero , proof-p) (suc q , proof-q) (suc r , proof-r) (zero , proof-s) proof-rs proof-sp proof-pq i j) = base
deletion (twoGenCommutativity1 (zero , proof-p) (zero , proof-q) (suc r , proof-r) (suc s , proof-s) proof-rs proof-sp proof-pq i j) = gen (r , pred proof-r) (s , pred proof-s) (pred proof-rs) i
deletion (twoGenCommutativity1 (zero , proof-p) (suc q , proof-q) (suc r , proof-r) (suc s , proof-s) proof-rs proof-sp proof-pq i j) = gen (r , pred proof-r) (s , pred proof-s) (pred proof-rs) i
deletion (twoGenCommutativity1 (suc p , proof-p) (zero , proof-q) (suc r , proof-r) (suc s , proof-s) proof-rs proof-sp proof-pq i j) = gen (r , pred proof-r) (s , pred proof-s) (pred proof-rs) i
deletion (twoGenCommutativity1 (suc p , proof-p) (suc q , proof-q) (zero , proof-r) (zero , proof-s) proof-rs proof-sp proof-pq i j) =  gen (p , pred proof-p) (q , pred proof-q) (pred proof-pq) j
deletion (twoGenCommutativity1 (suc p , proof-p) (suc q , proof-q) (suc r , proof-r) (zero , proof-s) proof-rs proof-sp proof-pq i j) =  gen (p , pred proof-p) (q , pred proof-q) (pred proof-pq) j

-- only two cases that are possible, either r is zero or it is not
deletion (twoGenCommutativity1 (suc p , proof-p) (suc q , proof-q) (zero , proof-r) (suc s , proof-s) proof-rs proof-sp proof-pq i j) = gen (p , pred proof-p) (q , pred proof-q) (pred proof-pq) j
deletion (twoGenCommutativity1 (suc p , proof-p) (suc q , proof-q) (suc r , proof-r) (suc s , proof-s) proof-rs proof-sp proof-pq i j) = twoGenCommutativity1 (p , pred proof-p) (q , pred proof-q) (r , pred proof-r) (s , pred proof-s) (pred proof-rs) (pred proof-sp) (pred proof-pq) i j




-- Commutivity case 2 : p < r < s < q ⇒ (gen p q ) · (gen r s) ≡ (gen r s) ∙ (gen p q)
-- these cases are impossible
deletion (twoGenCommutativity2 (zero , proof-p) (zero , proof-q) (zero , proof-r) (zero , proof-s) proof-pr proof-rs proof-sq proof-pq i j) = base
deletion (twoGenCommutativity2 (zero , proof-p) (zero , proof-q) (zero , proof-r) (suc s , proof-s) proof-pr proof-rs proof-sq proof-pq i j) = base
deletion (twoGenCommutativity2 (zero , proof-p) (zero , proof-q) (suc r , proof-r) (zero , proof-s) proof-pr proof-rs proof-sq proof-pq i j) = base
deletion (twoGenCommutativity2 (zero , proof-p) (zero , proof-q) (suc r , proof-r) (suc s , proof-s) proof-pr proof-rs proof-sq proof-pq i j) = gen (r , pred proof-r) (s , pred proof-s) (pred proof-rs) i
deletion (twoGenCommutativity2 (zero , proof-p) (suc q , proof-q) (zero , proof-r) (zero , proof-s) proof-pr proof-rs proof-sq proof-pq i j) = base
deletion (twoGenCommutativity2 (zero , proof-p) (suc q , proof-q) (zero , proof-r) (suc s , proof-s) proof-pr proof-rs proof-sq proof-pq i j) = base
deletion (twoGenCommutativity2 (zero , proof-p) (suc q , proof-q) (suc r , proof-r) (zero , proof-s) proof-pr proof-rs proof-sq proof-pq i j) = base
deletion (twoGenCommutativity2 (suc p , proof-p) (zero , proof-q) (zero , proof-r) (zero , proof-s) proof-pr proof-rs proof-sq proof-pq i j) = base
deletion (twoGenCommutativity2 (suc p , proof-p) (zero , proof-q) (zero , proof-r) (suc s , proof-s) proof-pr proof-rs proof-sq proof-pq i j) = base
deletion (twoGenCommutativity2 (suc p , proof-p) (zero , proof-q) (suc r , proof-r) (zero , proof-s) proof-pr proof-rs proof-sq proof-pq i j) = base
deletion (twoGenCommutativity2 (suc p , proof-p) (zero , proof-q) (suc r , proof-r) (suc s , proof-s) proof-pr proof-rs proof-sq proof-pq i j) = gen (r , pred proof-r) (s , pred proof-s) (pred proof-rs) i
deletion (twoGenCommutativity2 (suc p , proof-p) (suc q , proof-q) (zero , proof-r) (zero , proof-s) proof-pr proof-rs proof-sq proof-pq i j) = gen (p , pred proof-p) (q , pred proof-q) (pred proof-pq) j
deletion (twoGenCommutativity2 (suc p , proof-p) (suc q , proof-q) (zero , proof-r) (suc s , proof-s) proof-pr proof-rs proof-sq proof-pq i j) = gen (p , pred proof-p) (q , pred proof-q) (pred proof-pq) j
deletion (twoGenCommutativity2 (suc p , proof-p) (suc q , proof-q) (suc r , proof-r) (zero , proof-s) proof-pr proof-rs proof-sq proof-pq i j) = gen (p , pred proof-p) (q , pred proof-q) (pred proof-pq) j

-- only two cases are possible, p = 0 or p != 0 and r s q > 0
deletion (twoGenCommutativity2 (zero , proof-p) (suc q , proof-q) (suc r , proof-r) (suc s , proof-s) proof-pr proof-rs proof-sq proof-pq i j) = gen (r , pred proof-r) (s , pred proof-s) (pred proof-rs) i
deletion (twoGenCommutativity2 (suc p , proof-p) (suc q , proof-q) (suc r , proof-r) (suc s , proof-s) proof-pr proof-rs proof-sq proof-pq i j) = twoGenCommutativity2 (p , pred proof-p) (q , pred proof-q) (r , pred proof-r) (s , pred proof-s) (pred proof-pr) (pred proof-rs) (pred proof-sq) (pred proof-pq) i j




-- r < p < q
-- impossible cases
deletion (threeGenCommutativityConnector (zero , proof-r) (zero , proof-p) (zero , proof-q) proof-rp proof-pq proof-rq i) = base
deletion (threeGenCommutativityConnector (zero , proof-r) (zero , proof-p) (suc q , proof-q) proof-rp proof-pq proof-rq i) = base
deletion (threeGenCommutativityConnector (zero , proof-r) (suc p , proof-p) (zero , proof-q) proof-rp proof-pq proof-rq i) = base
deletion (threeGenCommutativityConnector (suc r , proof-r) (zero , proof-p) (zero , proof-q) proof-rp proof-pq proof-rq i) = base
deletion (threeGenCommutativityConnector (suc r , proof-r) (zero , proof-p) (suc q , proof-q) proof-rp proof-pq proof-rq i) = gen (r , pred proof-r) (q , pred proof-q) (pred proof-rq) i
deletion (threeGenCommutativityConnector (suc r , proof-r) (suc p , proof-p) (zero , proof-q) proof-rp proof-pq proof-rq i) = gen  (r , pred proof-r) (p , pred proof-p) (pred proof-rp) i


-- only possibele cases
deletion (threeGenCommutativityConnector (zero , proof-r) (suc p , proof-p) (suc q , proof-q) proof-rp proof-pq proof-rq i) = gen (p , pred proof-p) (q , pred proof-q) (pred proof-pq) i
deletion (threeGenCommutativityConnector (suc r , proof-r) (suc p , proof-p) (suc q , proof-q) proof-rp proof-pq proof-rq i) = threeGenCommutativityConnector (r , pred proof-r) (p , pred proof-p) (q , pred proof-q) (pred proof-rp) (pred proof-pq) (pred proof-rq) i



-- if p or q = 0, then absurd case as no natural number r such that r < 0

--impossible case
deletion (threeGenCommutativityLeft (zero , proof-r) (zero , proof-p) (zero , proof-q) proof-rp proof-pq proof-rq i j) = base
deletion (threeGenCommutativityLeft (zero , proof-r) (zero , proof-p) (suc q , proof-q) proof-rp proof-pq proof-rq i j) = base
deletion (threeGenCommutativityLeft (zero , proof-r) (suc p , proof-p) (zero , proof-q) proof-rp proof-pq proof-rq i j) = base
deletion (threeGenCommutativityLeft (suc r , proof-r) (zero , proof-p) (zero , proof-q) proof-rp proof-pq proof-rq i j) = base
deletion (threeGenCommutativityLeft (suc r , proof-r) (zero , proof-p) (suc q , proof-q) proof-rp proof-pq proof-rq i j) = gen (r , pred proof-r)  (q , pred proof-q) (pred proof-rq) (i ∧ ~ j)
deletion (threeGenCommutativityLeft (suc r , proof-r) (suc p , proof-p) (zero , proof-q) proof-rp proof-pq proof-rq i j) = gen  (r , pred proof-r) (p , pred proof-p) (pred proof-rp)  i


-- only cases that are possible
deletion (threeGenCommutativityLeft (zero , proof-r) (suc p , proof-p) (suc q , proof-q) proof-rp proof-pq proof-rq i j) = gen (p , pred proof-p) (q , pred proof-q) (pred proof-pq) ( i ∨ j  )
deletion (threeGenCommutativityLeft (suc r , proof-r) (suc p , proof-p) (suc q , proof-q) proof-rp proof-pq proof-rq i j) = threeGenCommutativityLeft (r , pred proof-r) (p , pred proof-p) (q , pred proof-q) (pred proof-rp) (pred proof-pq) (pred proof-rq) i j



-- impossible case
deletion (threeGenCommutativityMiddle (zero , proof-r) (zero , proof-p) (zero , proof-q) proof-rp proof-pq proof-rq i j) = base
deletion (threeGenCommutativityMiddle (zero , proof-r) (zero , proof-p) (suc q , proof-q) proof-rp proof-pq proof-rq i j) = base
deletion (threeGenCommutativityMiddle (zero , proof-r) (suc p , proof-p) (zero , proof-q) proof-rp proof-pq proof-rq i j) = base
deletion (threeGenCommutativityMiddle (suc r , proof-r) (zero , proof-p) (zero , proof-q) proof-rp proof-pq proof-rq i j) = base
deletion (threeGenCommutativityMiddle (suc r , proof-r) (zero , proof-p) (suc q , proof-q) proof-rp proof-pq proof-rq i j) = gen (r , pred proof-r)  (q , pred proof-q) (pred proof-rq)  i
deletion (threeGenCommutativityMiddle (suc r , proof-r) (suc p , proof-p) (zero , proof-q) proof-rp proof-pq proof-rq i j) = gen  (r , pred proof-r) (p , pred proof-p) (pred proof-rp) ( i ∨ j  )


-- only cases that are possible
deletion (threeGenCommutativityMiddle (zero , proof-r) (suc p , proof-p) (suc q , proof-q) proof-rp proof-pq proof-rq i j) = gen (p , pred proof-p) (q , pred proof-q) (pred proof-pq) ( i ∧ ~ j  )
deletion (threeGenCommutativityMiddle (suc r , proof-r) (suc p , proof-p) (suc q , proof-q) proof-rp proof-pq proof-rq i j) = threeGenCommutativityMiddle (r , pred proof-r) (p , pred proof-p) (q , pred proof-q) (pred proof-rp) (pred proof-pq) (pred proof-rq) i j




deletion (threeGenCommutativityRight (zero , proof-r) (zero , proof-p) (zero , proof-q) proof-rp proof-pq proof-rq i j) = base
deletion (threeGenCommutativityRight (zero , proof-r) (zero , proof-p) (suc q , proof-q) proof-rp proof-pq proof-rq i j) = base
deletion (threeGenCommutativityRight (zero , proof-r) (suc p , proof-p) (zero , proof-q) proof-rp proof-pq proof-rq i j) = base
deletion (threeGenCommutativityRight (suc r , proof-r) (zero , proof-p) (zero , proof-q) proof-rp proof-pq proof-rq i j) = base
deletion (threeGenCommutativityRight (suc r , proof-r) (zero , proof-p) (suc q , proof-q) proof-rp proof-pq proof-rq i j) = gen (r , pred proof-r)  (q , pred proof-q) (pred proof-rq) (  i ∨ j )
deletion (threeGenCommutativityRight (suc r , proof-r) (suc p , proof-p) (zero , proof-q) proof-rp proof-pq proof-rq i j) = gen  (r , pred proof-r) (p , pred proof-p) (pred proof-rp) ( i ∧ ~ j  )

deletion (threeGenCommutativityRight (zero , proof-r) (suc p , proof-p) (suc q , proof-q) proof-rp proof-pq proof-rq i j) = gen (p , pred proof-p) (q , pred proof-q) (pred proof-pq)  i
deletion (threeGenCommutativityRight (suc r , proof-r) (suc p , proof-p) (suc q , proof-q) proof-rp proof-pq proof-rq i j) = threeGenCommutativityRight (r , pred proof-r) (p , pred proof-p) (q , pred proof-q) (pred proof-rp) (pred proof-pq) (pred proof-rq) i j




--impossible cases
deletion (fourGenCommutativityConnector (zero , proof-r) (zero , proof-p) (zero , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i) = base
deletion (fourGenCommutativityConnector (zero , proof-r) (zero , proof-p) (zero , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i) = base
deletion (fourGenCommutativityConnector (zero , proof-r) (zero , proof-p) (suc s , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i) = base
deletion (fourGenCommutativityConnector (zero , proof-r) (zero , proof-p) (suc s , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i) = gen (s , pred proof-s) (q , pred proof-q) (pred proof-sq) i
deletion (fourGenCommutativityConnector (zero , proof-r) (suc p , proof-p) (zero , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i) = base
deletion (fourGenCommutativityConnector (zero , proof-r) (suc p , proof-p) (zero , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i) = gen (p , pred proof-p) (q , pred proof-q) (pred proof-pq) i
deletion (fourGenCommutativityConnector (zero , proof-r) (suc p , proof-p) (suc s , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i) = base
deletion (fourGenCommutativityConnector (suc r , proof-r) (zero , proof-p) (zero , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i) = base
deletion (fourGenCommutativityConnector (suc r , proof-r) (zero , proof-p) (zero , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i) = gen (r , pred proof-r) (q , pred proof-q) (pred proof-rq) i
deletion (fourGenCommutativityConnector (suc r , proof-r) (zero , proof-p) (suc s , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i) = base
deletion (fourGenCommutativityConnector (suc r , proof-r) (zero , proof-p) (suc s , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i) = base
deletion (fourGenCommutativityConnector (suc r , proof-r) (suc p , proof-p) (zero , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i) = base
deletion (fourGenCommutativityConnector (suc r , proof-r) (suc p , proof-p) (zero , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i) =  base   -- suspicious
deletion (fourGenCommutativityConnector (suc r , proof-r) (suc p , proof-p) (suc s , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i) = base

--possible cases
deletion (fourGenCommutativityConnector (zero , proof-r) (suc p , proof-p) (suc s , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i) =
   ((gen (p , pred proof-p) (q , pred proof-q) (pred proof-pq)) ∙ (gen (s , pred proof-s) (q , pred proof-q) (pred proof-sq)) ) i

  --gen (p , pred proof-p) (s , pred proof-s) (pred proof-ps) i -- questionable

deletion (fourGenCommutativityConnector (suc r , proof-r) (suc p , proof-p) (suc s , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i) =
  fourGenCommutativityConnector (r , pred proof-r) (p , pred proof-p) (s , pred proof-s) (q , pred proof-q) (pred proof-rp) (pred proof-ps) (pred proof-sq) (pred proof-rq) (pred proof-pq) i


--impossible cases
deletion (fourGenCommutativityComposition (zero , proof-r) (zero , proof-p) (zero , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i j) = base
deletion (fourGenCommutativityComposition (zero , proof-r) (zero , proof-p) (zero , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i j) = base
deletion (fourGenCommutativityComposition (zero , proof-r) (zero , proof-p) (suc s , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i j) = base
deletion (fourGenCommutativityComposition (zero , proof-r) (zero , proof-p) (suc s , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i j) = gen (s , pred proof-s) (q , pred proof-q) (pred proof-sq) (i ∧ ( ~ j))
deletion (fourGenCommutativityComposition (zero , proof-r) (suc p , proof-p) (zero , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i j) = base
deletion (fourGenCommutativityComposition (zero , proof-r) (suc p , proof-p) (zero , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i j) = gen (p , pred proof-p) (q , pred proof-q) (pred proof-pq) i
deletion (fourGenCommutativityComposition (zero , proof-r) (suc p , proof-p) (suc s , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i j) = base
deletion (fourGenCommutativityComposition (suc r , proof-r) (zero , proof-p) (zero , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i j) = base
deletion (fourGenCommutativityComposition (suc r , proof-r) (zero , proof-p) (zero , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i j) = gen (r , pred proof-r) (q , pred proof-q) (pred proof-rq) (i ∨ j)
deletion (fourGenCommutativityComposition (suc r , proof-r) (zero , proof-p) (suc s , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i j) = base
deletion (fourGenCommutativityComposition (suc r , proof-r) (zero , proof-p) (suc s , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i j) = ⊥.rec {A = Square (gen (r , pred proof-r) (q , pred proof-q) (pred proof-rq)) (sym (gen (s , pred proof-s) (q , pred proof-q) (pred proof-sq))) refl refl } (¬-<-zero proof-rp) i j
deletion (fourGenCommutativityComposition (suc r , proof-r) (suc p , proof-p) (zero , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i j) = base
deletion (fourGenCommutativityComposition (suc r , proof-r) (suc p , proof-p) (zero , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i j) = ⊥.rec {A = Square (gen (r , pred proof-r) (q , pred proof-q) (pred proof-rq)) refl refl (gen (p , pred proof-p) (q , pred proof-q) (pred proof-pq)) } (¬-<-zero proof-ps) i j
deletion (fourGenCommutativityComposition (suc r , proof-r) (suc p , proof-p) (suc s , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i j) = base



-- Square p (r ·· p ·· q) (sym r ) q
-- Square refl


-- possible cases
--deletion (fourGenCommutativityComposition (zero , proof-r) (suc p , proof-p) (suc s , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i j) =  ((gen (p , pred proof-p) (q , pred proof-q) (pred (<-trans proof-ps proof-sq))) ∙ (sym (gen (s , pred proof-s) (q , pred proof-q) (pred proof-sq)) )) {!  !} --gen (p , pred proof-p) (s , pred proof-s) (pred proof-ps) {!  !}
deletion (fourGenCommutativityComposition (zero , proof-r) (suc p , proof-p) (suc s , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i j)
  -- = {!   !}
  -- = lemma2 (doubleCompPath-filler refl
  --     (gen (p , pred proof-p) (q , pred proof-q) (pred {!   !}))
  --     (sym (gen (s , pred proof-s) (q , pred proof-q) (pred {!   !} ))))
  --     i j
  = compPath-filler (gen (p , pred proof-p) ( q , pred proof-q  ) ( pred proof-pq  )) ( gen (s , pred proof-s) (q , pred proof-q) ( pred proof-sq) )  (~ j) i


deletion (fourGenCommutativityComposition (suc r , proof-r) (suc p , proof-p) (suc s , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i j) = fourGenCommutativityComposition (r , pred proof-r) (p , pred proof-p) (s , pred proof-s) (q , pred proof-q) (pred proof-rp) (pred proof-ps) (pred proof-sq) (pred proof-rq) (pred proof-pq) i j



--impossible case

deletion (fourGenCommutativity (zero , proof-r) (zero , proof-p) (zero , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rs proof-rq proof-pq i j) = base
deletion (fourGenCommutativity (zero , proof-r) (zero , proof-p) (zero , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rs proof-rq proof-pq i j) = base
deletion (fourGenCommutativity (zero , proof-r) (zero , proof-p) (suc s , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rs proof-rq proof-pq i j) = base
deletion (fourGenCommutativity (zero , proof-r) (zero , proof-p) (suc s , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rs proof-rq proof-pq i j) = gen (s ,  pred proof-s  ) (q ,  pred proof-q  ) ( pred proof-sq  )  i
deletion (fourGenCommutativity (zero , proof-r) (suc p , proof-p) (zero , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rs proof-rq proof-pq i j) = base
deletion (fourGenCommutativity (zero , proof-r) (suc p , proof-p) (zero , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rs proof-rq proof-pq i j) =  gen (p , pred proof-p) (q , pred proof-q) (pred proof-pq) i
deletion (fourGenCommutativity (zero , proof-r) (suc p , proof-p) (suc s , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rs proof-rq proof-pq i j) = base
deletion (fourGenCommutativity (suc r , proof-r) (zero , proof-p) (zero , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rs proof-rq proof-pq i j) = base
deletion (fourGenCommutativity (suc r , proof-r) (zero , proof-p) (zero , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rs proof-rq proof-pq i j) = gen (r , pred proof-r) (q , pred proof-q) (pred proof-rq) i
deletion (fourGenCommutativity (suc r , proof-r) (zero , proof-p) (suc s , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rs proof-rq proof-pq i j) =  gen (r , pred proof-r) (s , pred proof-s) (pred proof-rs) j
deletion (fourGenCommutativity (suc r , proof-r) (zero , proof-p) (suc s , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rs proof-rq proof-pq i j) =   gen (r , pred proof-r) (s , pred proof-s) (pred proof-rs) j
deletion (fourGenCommutativity (suc r , proof-r) (suc p , proof-p) (zero , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rs proof-rq proof-pq i j) = base
deletion (fourGenCommutativity (suc r , proof-r) (suc p , proof-p) (zero , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rs proof-rq proof-pq i j) = base
deletion (fourGenCommutativity (suc r , proof-r) (suc p , proof-p) (suc s , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rs proof-rq proof-pq i j) =  gen (r , pred proof-r) (s , pred proof-s) (pred proof-rs) j



-- possible cases
deletion {n = n} (fourGenCommutativity (zero , proof-r) (suc p , proof-p) (suc s , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rs proof-rq proof-pq i j) =
  ((gen (p , pred proof-p) (q , pred proof-q) (pred proof-pq)) ∙ (gen (s , pred proof-s) (q , pred proof-q) (pred proof-sq))) i

-- fourGenCommutativityConnector (zero , {! zero-≤ {n = n}  !}) (p , pred proof-p) (s , pred proof-s) (q , pred proof-q) {!  !} (pred proof-ps) (pred proof-sq) i
deletion (fourGenCommutativity (suc r , proof-r) (suc p , proof-p) (suc s , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rs proof-rq proof-pq i j) =  fourGenCommutativity (r , pred proof-r) (p , pred proof-p) (s , pred proof-s) (q , pred proof-q) (pred proof-rp) (pred  proof-ps) (pred  proof-sq) (pred proof-rs) (pred proof-rq) (pred proof-pq) i j
