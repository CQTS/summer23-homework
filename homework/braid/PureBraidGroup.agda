-- {-# OPTIONS --safe #-}


module homework.braid.PureBraidGroup where
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat.Base
open import Cubical.Data.Fin.Base
open import Cubical.Data.Nat.Order
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

  commutativity1 : (p q r s : Fin n) → (proof-rs : toℕ r < toℕ s)
                          → ( proof-sp : toℕ s < toℕ p)
                          → ( proof-pq : toℕ p < toℕ q)
                          →  Square (gen p q proof-pq)  (gen p q proof-pq) (gen r s proof-rs ) (gen r s proof-rs)

  commutativity2 : (p q r s : Fin n) → (proof-pr : toℕ p < toℕ r)
                          → ( proof-rs : toℕ r < toℕ s)
                          → ( proof-sq : toℕ s < toℕ q)
                          → ( proof-pq : toℕ p < toℕ q) -- redundant

                          →  Square (gen p q proof-pq)  (gen p q proof-pq) (gen r s proof-rs) (gen r s proof-rs)




--               A r q                             A r q                              sym (A r p)
--             b - - - > b                       b - - - > b                         b - - - > b
--            ^         ^                       ^         ^                          ^         ^
--     A r p  |         |  3wayCommon    A r p  |         |              3wayCommon  |         |  A p q
--            |         |                       |         |  sym (A p q)             |         |
--            b — — — > b                       b — — — > b                          b — — — > b
--             sym (A p q)                       3wayCommon                             A r q

  threewayCommutativityCommon : (r p q : Fin n) → (proof-rp : toℕ r < toℕ p) → (proof-pq : toℕ p < toℕ q) → (proof-rq : toℕ r < toℕ q) → base ≡ base

  threewayCommutativityLeft : (r p q : Fin n) → (proof-rp : toℕ r < toℕ p) → (proof-pq : toℕ p < toℕ q) → (proof-rq : toℕ r < toℕ q) → Square
                                                                                                                                        (gen p q proof-pq)
                                                                                                                                        (sym (gen r q proof-rq))
                                                                                                                                        (threewayCommutativityCommon r p q proof-rp proof-pq proof-rq)
                                                                                                                                        (gen r p proof-rp )


  threewayCommutativityRight : (r p q : Fin n) → (proof-rp : toℕ r < toℕ p) → (proof-pq : toℕ p < toℕ q) → (proof-rq : toℕ r < toℕ q) → Square
                                                                                                                                          (gen r p proof-rp)
                                                                                                                                          (sym (gen p q proof-pq))
                                                                                                                                          (threewayCommutativityCommon r p q proof-rp proof-pq proof-rq)
                                                                                                                                          (gen r q proof-rq)

  threewayCommutativityTop : (r p q : Fin n) → (proof-rp : toℕ r < toℕ p) → (proof-pq : toℕ p < toℕ q) → (proof-rq : toℕ r < toℕ q) → Square
                                                                                                                                        (gen r q proof-rq)
                                                                                                                                        (sym (gen r p proof-rp))
                                                                                                                                        (threewayCommutativityCommon r p q proof-rp proof-pq proof-rq)
                                                                                                                                        (gen p q proof-pq)

  fourwayCommutativityConnector : (r p s q : Fin n) → (proof-rp : toℕ r < toℕ p) → (proof-ps : toℕ p < toℕ s) → (proof-sq : toℕ s < toℕ q) → (proof-rq : toℕ r < toℕ q) → (proof-pq : toℕ p < toℕ q) → base ≡ base

      --           A p q
      --        b ­- - - > b
      --        ^         ^
      --   A r q|         |  sym (A s q)
      --        |         |
      --        b - - - > b
      --            Conn

  fourwayCommutativityComposition : (r p s q : Fin n) → (proof-rp : toℕ r < toℕ p) → (proof-ps : toℕ p < toℕ s) → (proof-sq : toℕ s < toℕ q) → (proof-rq : toℕ r < toℕ q) → (proof-pq : toℕ p < toℕ q) → Square 
                                                                                                                                                                                                            (gen r q proof-rq)
                                                                                                                                                                                                            (sym (gen s q proof-sq))
                                                                                                                                                                                                            (fourwayCommutativityConnector r p s q proof-rp proof-ps proof-sq proof-rq proof-pq )
                                                                                                                                                                                                            (gen p q proof-pq)

  fourwayCommutativity : (r p s q : Fin n) → (proof-rp : toℕ r < toℕ p) → (proof-ps : toℕ p < toℕ s) → (proof-sq : toℕ s < toℕ q) → (proof-rs : toℕ r < toℕ s) → (proof-rq : toℕ r < toℕ q) → (proof-pq : toℕ p < toℕ q) → Square
                                                                                                                                                                                                                              (gen r s proof-rs)
                                                                                                                                                                                                                              (gen r s proof-rs) 
                                                                                                                                                                                                                              (fourwayCommutativityConnector r p s q proof-rp proof-ps proof-sq proof-rq proof-pq) 
                                                                                                                                                                                                                              (fourwayCommutativityConnector r p s q proof-rp proof-ps proof-sq proof-rq proof-pq)






addGen : {n : ℕ} (b : BPureBraid' n) → BPureBraid' (suc n)
addGen base = base
addGen (gen (m , proof-m) (n , proof-n) constraint i) = gen (m , ≤-suc proof-m) (n , ≤-suc proof-n) constraint i
addGen (commutativity1 (p , proof-p) (q , proof-q) (r , proof-r) (s , proof-s) proof-rs proof-sp proof-pq i j) = commutativity1 (p , ≤-suc proof-p) (q , ≤-suc proof-q) (r , ≤-suc proof-r) (s , ≤-suc proof-s) proof-rs proof-sp proof-pq i j
addGen (commutativity2 (p , proof-p) (q , proof-q) (r , proof-r) (s , proof-s) proof-pr proof-rs proof-sq proof-pq i j) = commutativity2 (p , ≤-suc proof-p ) ( q , ≤-suc proof-q) (r , ≤-suc proof-r) (s , ≤-suc proof-s) proof-pr  proof-rs proof-sq proof-pq i j


addGen (threewayCommutativityCommon (r , proof-r) (p , proof-p) (q , proof-q) proof-rp proof-pq proof-rq i)  = threewayCommutativityCommon ( r , ≤-suc proof-r) (p , ≤-suc proof-p) (q , ≤-suc proof-q) proof-rp proof-pq proof-rq i
addGen (threewayCommutativityLeft (r , proof-r) (p , proof-p) (q , proof-q)  proof-rp proof-pq proof-rq i j) = threewayCommutativityLeft (r , ≤-suc proof-r) (p , ≤-suc proof-p) (q , ≤-suc proof-q) proof-rp proof-pq proof-rq i j
addGen (threewayCommutativityRight (r , proof-r) (p , proof-p) (q , proof-q) proof-rp proof-pq proof-rq i j) = threewayCommutativityRight (r , ≤-suc proof-r) (p , ≤-suc proof-p) (q , ≤-suc proof-q) proof-rp proof-pq proof-rq i j
addGen (threewayCommutativityTop (r , proof-r) (p , proof-p) (q , proof-q)  proof-rp proof-pq proof-rq i j)  =  threewayCommutativityTop (r , ≤-suc proof-r) (p , ≤-suc proof-p) (q , ≤-suc proof-q) proof-rp proof-pq proof-rq i j

addGen (fourwayCommutativityComposition (r , proof-r) (p , proof-p) (s , proof-s) (q , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i j) = fourwayCommutativityComposition (r , ≤-suc proof-r) (p , ≤-suc proof-p) (s , ≤-suc proof-s) (q , ≤-suc proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i j
addGen (fourwayCommutativity (r , proof-r) (p , proof-p) (s , proof-s) (q , proof-q) proof-rp proof-ps proof-sq proof-rs proof-rq proof-pq i j) = fourwayCommutativity (r , ≤-suc proof-r) (p , ≤-suc proof-p) (s , ≤-suc proof-s) (q , ≤-suc proof-q) proof-rp proof-ps proof-sq proof-rs proof-rq proof-pq i j
addGen (fourwayCommutativityConnector (r , proof-r) (p , proof-p) (s , proof-s) (q , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i ) = fourwayCommutativityConnector (r , ≤-suc proof-r) (p , ≤-suc proof-p) (s , ≤-suc proof-s) (q , ≤-suc proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i



deletion : {n : ℕ} (b : BPureBraid' (suc n)) → BPureBraid' n
deletion base = base

deletion (gen (zero , proof-p) (q , proof-q) constraint i) = base
deletion (gen (suc p , proof-p) (zero , proof-q) constraint i) = base
deletion (gen (suc p , proof-p) (suc q , proof-q) constraint i) = gen ( p , pred-≤-pred proof-p) (q , pred-≤-pred proof-q) (pred-≤-pred constraint) i


-- Commutivity case 1 : r < s < p < q  ⇒ (gen p q ) · (gen r s) ≡ (gen r s) ∙ (gen p q)
-- these cases are absurd and will not be used
deletion (commutativity1 (zero , proof-p) (zero , proof-q) (zero , proof-r) (zero , proof-s) proof-rs proof-sp proof-pq i j) = base
deletion (commutativity1 (zero , proof-p) (zero , proof-q) (zero , proof-r) (suc s , proof-s) proof-rs proof-sp proof-pq i j) = base
deletion (commutativity1 (zero , proof-p) (zero , proof-q) (suc r , proof-r) (zero , proof-s) proof-rs proof-sp proof-pq i j) =  base
deletion (commutativity1 (suc p , proof-p) (zero , proof-q) (zero , proof-r) (zero , proof-s) proof-rs proof-sp proof-pq i j) =  base 
deletion (commutativity1 (suc p , proof-p) (zero , proof-q) (zero , proof-r) (suc s , proof-s) proof-rs proof-sp proof-pq i j) = base 
deletion (commutativity1 (suc p , proof-p) (zero , proof-q) (suc r , proof-r) (zero , proof-s) proof-rs proof-sp proof-pq i j) = base 
deletion (commutativity1 (zero , proof-p) (suc q , proof-q) (zero , proof-r) (zero , proof-s) proof-rs proof-sp proof-pq i j) = base
deletion (commutativity1 (zero , proof-p) (suc q , proof-q) (zero , proof-r) (suc s , proof-s) proof-rs proof-sp proof-pq i j) = base
deletion (commutativity1 (zero , proof-p) (suc q , proof-q) (suc r , proof-r) (zero , proof-s) proof-rs proof-sp proof-pq i j) = base
deletion (commutativity1 (zero , proof-p) (zero , proof-q) (suc r , proof-r) (suc s , proof-s) proof-rs proof-sp proof-pq i j) = gen (r , pred-≤-pred proof-r) (s , pred-≤-pred proof-s) (pred-≤-pred proof-rs) i
deletion (commutativity1 (zero , proof-p) (suc q , proof-q) (suc r , proof-r) (suc s , proof-s) proof-rs proof-sp proof-pq i j) = gen (r , pred-≤-pred proof-r) (s , pred-≤-pred proof-s) (pred-≤-pred proof-rs) i
deletion (commutativity1 (suc p , proof-p) (zero , proof-q) (suc r , proof-r) (suc s , proof-s) proof-rs proof-sp proof-pq i j) = gen (r , pred-≤-pred proof-r) (s , pred-≤-pred proof-s) (pred-≤-pred proof-rs) i
deletion (commutativity1 (suc p , proof-p) (suc q , proof-q) (zero , proof-r) (zero , proof-s) proof-rs proof-sp proof-pq i j) =  gen (p , pred-≤-pred proof-p) (q , pred-≤-pred proof-q) (pred-≤-pred proof-pq) j
deletion (commutativity1 (suc p , proof-p) (suc q , proof-q) (suc r , proof-r) (zero , proof-s) proof-rs proof-sp proof-pq i j) =  gen (p , pred-≤-pred proof-p) (q , pred-≤-pred proof-q) (pred-≤-pred proof-pq) j

-- only two cases that are possible, either r is zero or it is not
deletion (commutativity1 (suc p , proof-p) (suc q , proof-q) (zero , proof-r) (suc s , proof-s) proof-rs proof-sp proof-pq i j) = gen (p , pred-≤-pred proof-p) (q , pred-≤-pred proof-q) (pred-≤-pred proof-pq) j
deletion (commutativity1 (suc p , proof-p) (suc q , proof-q) (suc r , proof-r) (suc s , proof-s) proof-rs proof-sp proof-pq i j) = commutativity1 (p , pred-≤-pred proof-p) (q , pred-≤-pred proof-q) (r , pred-≤-pred proof-r) (s , pred-≤-pred proof-s) (pred-≤-pred proof-rs) (pred-≤-pred proof-sp) (pred-≤-pred proof-pq) i j




-- Commutivity case 2 : p < r < s < q ⇒ (gen p q ) · (gen r s) ≡ (gen r s) ∙ (gen p q)
-- these cases are impossible
deletion (commutativity2 (zero , proof-p) (zero , proof-q) (zero , proof-r) (zero , proof-s) proof-pr proof-rs proof-sq proof-pq i j) = base
deletion (commutativity2 (zero , proof-p) (zero , proof-q) (zero , proof-r) (suc s , proof-s) proof-pr proof-rs proof-sq proof-pq i j) = base
deletion (commutativity2 (zero , proof-p) (zero , proof-q) (suc r , proof-r) (zero , proof-s) proof-pr proof-rs proof-sq proof-pq i j) = base
deletion (commutativity2 (zero , proof-p) (zero , proof-q) (suc r , proof-r) (suc s , proof-s) proof-pr proof-rs proof-sq proof-pq i j) = gen (r , pred-≤-pred proof-r) (s , pred-≤-pred proof-s) (pred-≤-pred proof-rs) i
deletion (commutativity2 (zero , proof-p) (suc q , proof-q) (zero , proof-r) (zero , proof-s) proof-pr proof-rs proof-sq proof-pq i j) = base
deletion (commutativity2 (zero , proof-p) (suc q , proof-q) (zero , proof-r) (suc s , proof-s) proof-pr proof-rs proof-sq proof-pq i j) = base
deletion (commutativity2 (zero , proof-p) (suc q , proof-q) (suc r , proof-r) (zero , proof-s) proof-pr proof-rs proof-sq proof-pq i j) = base
deletion (commutativity2 (suc p , proof-p) (zero , proof-q) (zero , proof-r) (zero , proof-s) proof-pr proof-rs proof-sq proof-pq i j) = base
deletion (commutativity2 (suc p , proof-p) (zero , proof-q) (zero , proof-r) (suc s , proof-s) proof-pr proof-rs proof-sq proof-pq i j) = base
deletion (commutativity2 (suc p , proof-p) (zero , proof-q) (suc r , proof-r) (zero , proof-s) proof-pr proof-rs proof-sq proof-pq i j) = base
deletion (commutativity2 (suc p , proof-p) (zero , proof-q) (suc r , proof-r) (suc s , proof-s) proof-pr proof-rs proof-sq proof-pq i j) = gen (r , pred-≤-pred proof-r) (s , pred-≤-pred proof-s) (pred-≤-pred proof-rs) i
deletion (commutativity2 (suc p , proof-p) (suc q , proof-q) (zero , proof-r) (zero , proof-s) proof-pr proof-rs proof-sq proof-pq i j) = gen (p , pred-≤-pred proof-p) (q , pred-≤-pred proof-q) (pred-≤-pred proof-pq) j
deletion (commutativity2 (suc p , proof-p) (suc q , proof-q) (zero , proof-r) (suc s , proof-s) proof-pr proof-rs proof-sq proof-pq i j) = gen (p , pred-≤-pred proof-p) (q , pred-≤-pred proof-q) (pred-≤-pred proof-pq) j
deletion (commutativity2 (suc p , proof-p) (suc q , proof-q) (suc r , proof-r) (zero , proof-s) proof-pr proof-rs proof-sq proof-pq i j) = gen (p , pred-≤-pred proof-p) (q , pred-≤-pred proof-q) (pred-≤-pred proof-pq) j

-- only two cases are possible, p = 0 or p != 0 and r s q > 0
deletion (commutativity2 (zero , proof-p) (suc q , proof-q) (suc r , proof-r) (suc s , proof-s) proof-pr proof-rs proof-sq proof-pq i j) = gen (r , pred-≤-pred proof-r) (s , pred-≤-pred proof-s) (pred-≤-pred proof-rs) i
deletion (commutativity2 (suc p , proof-p) (suc q , proof-q) (suc r , proof-r) (suc s , proof-s) proof-pr proof-rs proof-sq proof-pq i j) = commutativity2 (p , pred-≤-pred proof-p) (q , pred-≤-pred proof-q) (r , pred-≤-pred proof-r) (s , pred-≤-pred proof-s) (pred-≤-pred proof-pr) (pred-≤-pred proof-rs) (pred-≤-pred proof-sq) (pred-≤-pred proof-pq) i j




-- r < p < q
-- impossible cases
deletion (threewayCommutativityCommon (zero , proof-r) (zero , proof-p) (zero , proof-q) proof-rp proof-pq proof-rq i) = base
deletion (threewayCommutativityCommon (zero , proof-r) (zero , proof-p) (suc q , proof-q) proof-rp proof-pq proof-rq i) = base
deletion (threewayCommutativityCommon (zero , proof-r) (suc p , proof-p) (zero , proof-q) proof-rp proof-pq proof-rq i) = base
deletion (threewayCommutativityCommon (suc r , proof-r) (zero , proof-p) (zero , proof-q) proof-rp proof-pq proof-rq i) = base
deletion (threewayCommutativityCommon (suc r , proof-r) (zero , proof-p) (suc q , proof-q) proof-rp proof-pq proof-rq i) = gen (r , pred-≤-pred proof-r) (q , pred-≤-pred proof-q) (pred-≤-pred proof-rq) i
deletion (threewayCommutativityCommon (suc r , proof-r) (suc p , proof-p) (zero , proof-q) proof-rp proof-pq proof-rq i) = gen  (r , pred-≤-pred proof-r) (p , pred-≤-pred proof-p) (pred-≤-pred proof-rp) i


-- only possibele cases
deletion (threewayCommutativityCommon (zero , proof-r) (suc p , proof-p) (suc q , proof-q) proof-rp proof-pq proof-rq i) = gen (p , pred-≤-pred proof-p) (q , pred-≤-pred proof-q) (pred-≤-pred proof-pq) i
deletion (threewayCommutativityCommon (suc r , proof-r) (suc p , proof-p) (suc q , proof-q) proof-rp proof-pq proof-rq i) = threewayCommutativityCommon (r , pred-≤-pred proof-r) (p , pred-≤-pred proof-p) (q , pred-≤-pred proof-q) (pred-≤-pred proof-rp) (pred-≤-pred proof-pq) (pred-≤-pred proof-rq) i



-- if p or q = 0, then absurd case as no natural number r such that r < 0

--impossible case
deletion (threewayCommutativityLeft (zero , proof-r) (zero , proof-p) (zero , proof-q) proof-rp proof-pq proof-rq i j) = base
deletion (threewayCommutativityLeft (zero , proof-r) (zero , proof-p) (suc q , proof-q) proof-rp proof-pq proof-rq i j) = base
deletion (threewayCommutativityLeft (zero , proof-r) (suc p , proof-p) (zero , proof-q) proof-rp proof-pq proof-rq i j) = base
deletion (threewayCommutativityLeft (suc r , proof-r) (zero , proof-p) (zero , proof-q) proof-rp proof-pq proof-rq i j) = base
deletion (threewayCommutativityLeft (suc r , proof-r) (zero , proof-p) (suc q , proof-q) proof-rp proof-pq proof-rq i j) = gen (r , pred-≤-pred proof-r)  (q , pred-≤-pred proof-q) (pred-≤-pred proof-rq) {! (i ∧ ~ j)  !}
deletion (threewayCommutativityLeft (suc r , proof-r) (suc p , proof-p) (zero , proof-q) proof-rp proof-pq proof-rq i j) = gen  (r , pred-≤-pred proof-r) (p , pred-≤-pred proof-p) (pred-≤-pred proof-rp) {!   !}


-- only cases that are possible
deletion (threewayCommutativityLeft (zero , proof-r) (suc p , proof-p) (suc q , proof-q) proof-rp proof-pq proof-rq i j) = gen (p , pred-≤-pred proof-p) (q , pred-≤-pred proof-q) (pred-≤-pred proof-pq) {!   !}
deletion (threewayCommutativityLeft (suc r , proof-r) (suc p , proof-p) (suc q , proof-q) proof-rp proof-pq proof-rq i j) = threewayCommutativityLeft (r , pred-≤-pred proof-r) (p , pred-≤-pred proof-p) (q , pred-≤-pred proof-q) (pred-≤-pred proof-rp) (pred-≤-pred proof-pq) (pred-≤-pred proof-rq) i j



-- impossible case
deletion (threewayCommutativityRight (zero , proof-r) (zero , proof-p) (zero , proof-q) proof-rp proof-pq proof-rq i j) = base
deletion (threewayCommutativityRight (zero , proof-r) (zero , proof-p) (suc q , proof-q) proof-rp proof-pq proof-rq i j) = base
deletion (threewayCommutativityRight (zero , proof-r) (suc p , proof-p) (zero , proof-q) proof-rp proof-pq proof-rq i j) = base
deletion (threewayCommutativityRight (suc r , proof-r) (zero , proof-p) (zero , proof-q) proof-rp proof-pq proof-rq i j) = base
deletion (threewayCommutativityRight (suc r , proof-r) (zero , proof-p) (suc q , proof-q) proof-rp proof-pq proof-rq i j) = gen (r , pred-≤-pred proof-r)  (q , pred-≤-pred proof-q) (pred-≤-pred proof-rq) {!   !}
deletion (threewayCommutativityRight (suc r , proof-r) (suc p , proof-p) (zero , proof-q) proof-rp proof-pq proof-rq i j) = gen  (r , pred-≤-pred proof-r) (p , pred-≤-pred proof-p) (pred-≤-pred proof-rp) {!   !}


-- only cases that are possible
deletion (threewayCommutativityRight (zero , proof-r) (suc p , proof-p) (suc q , proof-q) proof-rp proof-pq proof-rq i j) = gen (p , pred-≤-pred proof-p) (q , pred-≤-pred proof-q) (pred-≤-pred proof-pq) {!   !}
deletion (threewayCommutativityRight (suc r , proof-r) (suc p , proof-p) (suc q , proof-q) proof-rp proof-pq proof-rq i j) = threewayCommutativityRight (r , pred-≤-pred proof-r) (p , pred-≤-pred proof-p) (q , pred-≤-pred proof-q) (pred-≤-pred proof-rp) (pred-≤-pred proof-pq) (pred-≤-pred proof-rq) i j




deletion (threewayCommutativityTop (zero , proof-r) (zero , proof-p) (zero , proof-q) proof-rp proof-pq proof-rq i j) = base
deletion (threewayCommutativityTop (zero , proof-r) (zero , proof-p) (suc q , proof-q) proof-rp proof-pq proof-rq i j) = base
deletion (threewayCommutativityTop (zero , proof-r) (suc p , proof-p) (zero , proof-q) proof-rp proof-pq proof-rq i j) = base
deletion (threewayCommutativityTop (suc r , proof-r) (zero , proof-p) (zero , proof-q) proof-rp proof-pq proof-rq i j) = base
deletion (threewayCommutativityTop (suc r , proof-r) (zero , proof-p) (suc q , proof-q) proof-rp proof-pq proof-rq i j) = gen (r , pred-≤-pred proof-r)  (q , pred-≤-pred proof-q) (pred-≤-pred proof-rq) {!   !}
deletion (threewayCommutativityTop (suc r , proof-r) (suc p , proof-p) (zero , proof-q) proof-rp proof-pq proof-rq i j) = gen  (r , pred-≤-pred proof-r) (p , pred-≤-pred proof-p) (pred-≤-pred proof-rp) {!   !}

deletion (threewayCommutativityTop (zero , proof-r) (suc p , proof-p) (suc q , proof-q) proof-rp proof-pq proof-rq i j) = gen (p , pred-≤-pred proof-p) (q , pred-≤-pred proof-q) (pred-≤-pred proof-pq) {!   !}
deletion (threewayCommutativityTop (suc r , proof-r) (suc p , proof-p) (suc q , proof-q) proof-rp proof-pq proof-rq i j) = threewayCommutativityTop (r , pred-≤-pred proof-r) (p , pred-≤-pred proof-p) (q , pred-≤-pred proof-q) (pred-≤-pred proof-rp) (pred-≤-pred proof-pq) (pred-≤-pred proof-rq) i j




--impossible cases
deletion (fourwayCommutativityConnector (zero , proof-r) (zero , proof-p) (zero , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i) = base
deletion (fourwayCommutativityConnector (zero , proof-r) (zero , proof-p) (zero , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i) = base
deletion (fourwayCommutativityConnector (zero , proof-r) (zero , proof-p) (suc s , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i) = base
deletion (fourwayCommutativityConnector (zero , proof-r) (zero , proof-p) (suc s , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i) = gen (s , pred-≤-pred proof-s) (q , pred-≤-pred proof-q) (pred-≤-pred proof-sq) i
deletion (fourwayCommutativityConnector (zero , proof-r) (suc p , proof-p) (zero , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i) = base
deletion (fourwayCommutativityConnector (zero , proof-r) (suc p , proof-p) (zero , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i) = gen (p , pred-≤-pred proof-p) (q , pred-≤-pred proof-q) (pred-≤-pred proof-pq) i 
deletion (fourwayCommutativityConnector (zero , proof-r) (suc p , proof-p) (suc s , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i) = base
deletion (fourwayCommutativityConnector (suc r , proof-r) (zero , proof-p) (zero , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i) = base
deletion (fourwayCommutativityConnector (suc r , proof-r) (zero , proof-p) (zero , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i) = gen (r , pred-≤-pred proof-r) (q , pred-≤-pred proof-q) (pred-≤-pred proof-rq) i
deletion (fourwayCommutativityConnector (suc r , proof-r) (zero , proof-p) (suc s , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i) = base
deletion (fourwayCommutativityConnector (suc r , proof-r) (zero , proof-p) (suc s , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i) = base  
deletion (fourwayCommutativityConnector (suc r , proof-r) (suc p , proof-p) (zero , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i) = base
deletion (fourwayCommutativityConnector (suc r , proof-r) (suc p , proof-p) (zero , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i) =  base   -- suspicious
deletion (fourwayCommutativityConnector (suc r , proof-r) (suc p , proof-p) (suc s , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i) = base

--possible cases
deletion (fourwayCommutativityConnector (zero , proof-r) (suc p , proof-p) (suc s , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i) =
   ((gen (p , pred-≤-pred proof-p) (q , pred-≤-pred proof-q) (pred-≤-pred proof-pq)) ∙ (gen (s , pred-≤-pred proof-s) (q , pred-≤-pred proof-q) (pred-≤-pred proof-sq)) ) i

  --gen (p , pred-≤-pred proof-p) (s , pred-≤-pred proof-s) (pred-≤-pred proof-ps) i -- questionable
  -- deletion (fourwayCommutativityConnector (zero , proof-r) (suc p , proof-p) (suc s , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i) = {!   !}
deletion (fourwayCommutativityConnector (suc r , proof-r) (suc p , proof-p) (suc s , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i) =
  fourwayCommutativityConnector (r , pred-≤-pred proof-r) (p , pred-≤-pred proof-p) (s , pred-≤-pred proof-s) (q , pred-≤-pred proof-q) (pred-≤-pred proof-rp) (pred-≤-pred proof-ps) (pred-≤-pred proof-sq) (pred-≤-pred proof-rq) (pred-≤-pred proof-pq) i


--impossible cases
deletion (fourwayCommutativityComposition (zero , proof-r) (zero , proof-p) (zero , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i j) = base
deletion (fourwayCommutativityComposition (zero , proof-r) (zero , proof-p) (zero , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i j) = base
deletion (fourwayCommutativityComposition (zero , proof-r) (zero , proof-p) (suc s , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i j) = base
deletion (fourwayCommutativityComposition (zero , proof-r) (zero , proof-p) (suc s , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i j) = gen (s , pred-≤-pred proof-s) (q , pred-≤-pred proof-q) (pred-≤-pred proof-sq) (i ∧ ( ~ j))
deletion (fourwayCommutativityComposition (zero , proof-r) (suc p , proof-p) (zero , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i j) = base
deletion (fourwayCommutativityComposition (zero , proof-r) (suc p , proof-p) (zero , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i j) = gen (p , pred-≤-pred proof-p) (q , pred-≤-pred proof-q) (pred-≤-pred proof-pq) i
deletion (fourwayCommutativityComposition (zero , proof-r) (suc p , proof-p) (suc s , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i j) = base
deletion (fourwayCommutativityComposition (suc r , proof-r) (zero , proof-p) (zero , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i j) = base
deletion (fourwayCommutativityComposition (suc r , proof-r) (zero , proof-p) (zero , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i j) = gen (r , pred-≤-pred proof-r) (q , pred-≤-pred proof-q) (pred-≤-pred proof-rq) (i ∨ j)
deletion (fourwayCommutativityComposition (suc r , proof-r) (zero , proof-p) (suc s , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i j) = base
deletion (fourwayCommutativityComposition (suc r , proof-r) (zero , proof-p) (suc s , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i j) = ⊥.rec {A = Square (gen (r , pred-≤-pred proof-r) (q , pred-≤-pred proof-q) (pred-≤-pred proof-rq)) (sym (gen (s , pred-≤-pred proof-s) (q , pred-≤-pred proof-q) (pred-≤-pred proof-sq))) refl refl } (¬-<-zero proof-rp) i j
deletion (fourwayCommutativityComposition (suc r , proof-r) (suc p , proof-p) (zero , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i j) = base
deletion (fourwayCommutativityComposition (suc r , proof-r) (suc p , proof-p) (zero , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i j) = ⊥.rec {A = Square (gen (r , pred-≤-pred proof-r) (q , pred-≤-pred proof-q) (pred-≤-pred proof-rq)) refl refl (gen (p , pred-≤-pred proof-p) (q , pred-≤-pred proof-q) (pred-≤-pred proof-pq)) } (¬-<-zero proof-ps) i j
deletion (fourwayCommutativityComposition (suc r , proof-r) (suc p , proof-p) (suc s , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i j) = base



-- Square p (r ·· p ·· q) (sym r ) q
-- Square refl


-- possible cases
--deletion (fourwayCommutativityComposition (zero , proof-r) (suc p , proof-p) (suc s , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i j) =  ((gen (p , pred-≤-pred proof-p) (q , pred-≤-pred proof-q) (pred-≤-pred (<-trans proof-ps proof-sq))) ∙ (sym (gen (s , pred-≤-pred proof-s) (q , pred-≤-pred proof-q) (pred-≤-pred proof-sq)) )) {!  !} --gen (p , pred-≤-pred proof-p) (s , pred-≤-pred proof-s) (pred-≤-pred proof-ps) {!  !}
deletion (fourwayCommutativityComposition (zero , proof-r) (suc p , proof-p) (suc s , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i j)
  -- = {!   !}
  -- = lemma2 (doubleCompPath-filler refl
  --     (gen (p , pred-≤-pred proof-p) (q , pred-≤-pred proof-q) (pred-≤-pred {!   !}))
  --     (sym (gen (s , pred-≤-pred proof-s) (q , pred-≤-pred proof-q) (pred-≤-pred {!   !} ))))
  --     i j
  = compPath-filler (gen (p , pred-≤-pred proof-p) ( q , pred-≤-pred proof-q  ) ( pred-≤-pred proof-pq  )) ( gen (s , pred-≤-pred proof-s) (q , pred-≤-pred proof-q) ( pred-≤-pred proof-sq) )  (~ j) i


deletion (fourwayCommutativityComposition (suc r , proof-r) (suc p , proof-p) (suc s , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i j) = fourwayCommutativityComposition (r , pred-≤-pred proof-r) (p , pred-≤-pred proof-p) (s , pred-≤-pred proof-s) (q , pred-≤-pred proof-q) (pred-≤-pred proof-rp) (pred-≤-pred proof-ps) (pred-≤-pred proof-sq) (pred-≤-pred proof-rq) (pred-≤-pred proof-pq) i j



--impossible case

deletion (fourwayCommutativity (zero , proof-r) (zero , proof-p) (zero , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rs proof-rq proof-pq i j) = base
deletion (fourwayCommutativity (zero , proof-r) (zero , proof-p) (zero , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rs proof-rq proof-pq i j) = base
deletion (fourwayCommutativity (zero , proof-r) (zero , proof-p) (suc s , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rs proof-rq proof-pq i j) = base
deletion (fourwayCommutativity (zero , proof-r) (zero , proof-p) (suc s , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rs proof-rq proof-pq i j) = gen (s ,  pred-≤-pred proof-s  ) (q ,  pred-≤-pred proof-q  ) ( pred-≤-pred proof-sq  )  i
deletion (fourwayCommutativity (zero , proof-r) (suc p , proof-p) (zero , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rs proof-rq proof-pq i j) = base
deletion (fourwayCommutativity (zero , proof-r) (suc p , proof-p) (zero , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rs proof-rq proof-pq i j) =  gen (p , pred-≤-pred proof-p) (q , pred-≤-pred proof-q) (pred-≤-pred proof-pq) i 
deletion (fourwayCommutativity (zero , proof-r) (suc p , proof-p) (suc s , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rs proof-rq proof-pq i j) = base
deletion (fourwayCommutativity (suc r , proof-r) (zero , proof-p) (zero , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rs proof-rq proof-pq i j) = base
deletion (fourwayCommutativity (suc r , proof-r) (zero , proof-p) (zero , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rs proof-rq proof-pq i j) = gen (r , pred-≤-pred proof-r) (q , pred-≤-pred proof-q) (pred-≤-pred proof-rq) i 
deletion (fourwayCommutativity (suc r , proof-r) (zero , proof-p) (suc s , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rs proof-rq proof-pq i j) =  gen (r , pred-≤-pred proof-r) (s , pred-≤-pred proof-s) (pred-≤-pred proof-rs) j 
deletion (fourwayCommutativity (suc r , proof-r) (zero , proof-p) (suc s , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rs proof-rq proof-pq i j) =   gen (r , pred-≤-pred proof-r) (s , pred-≤-pred proof-s) (pred-≤-pred proof-rs) j  
deletion (fourwayCommutativity (suc r , proof-r) (suc p , proof-p) (zero , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rs proof-rq proof-pq i j) = base
deletion (fourwayCommutativity (suc r , proof-r) (suc p , proof-p) (zero , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rs proof-rq proof-pq i j) = base
deletion (fourwayCommutativity (suc r , proof-r) (suc p , proof-p) (suc s , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rs proof-rq proof-pq i j) =  gen (r , pred-≤-pred proof-r) (s , pred-≤-pred proof-s) (pred-≤-pred proof-rs) j



-- possible cases
deletion {n = n} (fourwayCommutativity (zero , proof-r) (suc p , proof-p) (suc s , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rs proof-rq proof-pq i j) =
  ((gen (p , pred-≤-pred proof-p) (q , pred-≤-pred proof-q) (pred-≤-pred proof-pq)) ∙ (gen (s , pred-≤-pred proof-s) (q , pred-≤-pred proof-q) (pred-≤-pred proof-sq))) i

-- fourwayCommutativityConnector (zero , {! zero-≤ {n = n}  !}) (p , pred-≤-pred proof-p) (s , pred-≤-pred proof-s) (q , pred-≤-pred proof-q) {!  !} (pred-≤-pred proof-ps) (pred-≤-pred proof-sq) i
deletion (fourwayCommutativity (suc r , proof-r) (suc p , proof-p) (suc s , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rs proof-rq proof-pq i j) =  fourwayCommutativity (r , pred-≤-pred proof-r) (p , pred-≤-pred proof-p) (s , pred-≤-pred proof-s) (q , pred-≤-pred proof-q) (pred-≤-pred proof-rp) (pred-≤-pred  proof-ps) (pred-≤-pred  proof-sq) (pred-≤-pred proof-rs) (pred-≤-pred proof-rq) (pred-≤-pred proof-pq) i j
