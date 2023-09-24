{-# OPTIONS --safe #-}


module Braid.PureBraid where

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Fin
open import Cubical.Data.Nat.Order renaming (pred-≤-pred to pred ; ≤-suc to sucP ; suc-≤-suc to ssuc ; ¬-<-zero to !<0 ; ¬m<m to !m<m ;
                                             <-weaken to weaken; <-asym to asym ; <-trans to trans ; <→≢  to <!=)
open import Cubical.Data.Empty as ⊥






data BPureBraid (n : ℕ) :  Type where -- pure braid group of n strands
  base : BPureBraid n
  gen  : (p q : Fin n) → (proof-pq : toℕ p < toℕ q)  → base ≡ base

  twoGencommutativity1 : (p q r s : Fin n)
                          → (proof-rs : toℕ r < toℕ s)
                          → ( proof-sp : toℕ s < toℕ p)
                          → ( proof-pq : toℕ p < toℕ q)
                          →  Square (gen p q proof-pq)  (gen p q proof-pq) (gen r s proof-rs ) (gen r s proof-rs)

  twoGencommutativity2 : (p q r s : Fin n) 
                          → (proof-pr : toℕ p < toℕ r)
                          → ( proof-rs : toℕ r < toℕ s)
                          → ( proof-sq : toℕ s < toℕ q)
                          → ( proof-pq : toℕ p < toℕ q)
                          →  Square (gen p q proof-pq)  (gen p q proof-pq) (gen r s proof-rs) (gen r s proof-rs)




--               A r q                             A r q                              sym (A r p)
--             b - - - > b                       b - - - > b                         b - - - > b
--            ^         ^                       ^         ^                          ^         ^
--     A r p  |         |  3wayCommon    A r p  |         |              3wayCommon  |         |  A p q
--            |         |                       |         |  sym (A p q)             |         |
--            b — — — > b                       b — — — > b                          b — — — > b
--             sym (A p q)                       3wayCommon                             A r q

  threeGenCommutativityConnector : (r p q : Fin n) 
                                → (proof-rp : toℕ r < toℕ p) 
                                → (proof-pq : toℕ p < toℕ q) 
                                → (proof-rq : toℕ r < toℕ q) 
                                → base ≡ base

  threeGenCommutativityLeft : (r p q : Fin n) 
                                → (proof-rp : toℕ r < toℕ p) 
                                → (proof-pq : toℕ p < toℕ q) 
                                → (proof-rq : toℕ r < toℕ q) 
                                → Square
                                    (gen p q proof-pq)
                                    (sym (gen r q proof-rq))
                                    (threeGenCommutativityConnector r p q proof-rp proof-pq proof-rq)
                                    (gen r p proof-rp )

  threeGenCommutativityMiddle : (r p q : Fin n) 
                                → (proof-rp : toℕ r < toℕ p) 
                                → (proof-pq : toℕ p < toℕ q) 
                                → (proof-rq : toℕ r < toℕ q) 
                                → Square
                                    (gen r p proof-rp)
                                    (sym (gen p q proof-pq))
                                    (threeGenCommutativityConnector r p q proof-rp proof-pq proof-rq)
                                    (gen r q proof-rq)

                                                                                                                                      
  threeGenCommutativityRight : (r p q : Fin n) 
                                → (proof-rp : toℕ r < toℕ p) 
                                → (proof-pq : toℕ p < toℕ q) 
                                → (proof-rq : toℕ r < toℕ q) 
                                → Square
                                    (gen r q proof-rq)
                                    (sym (gen r p proof-rp))
                                    (threeGenCommutativityConnector r p q proof-rp proof-pq proof-rq)
                                    (gen p q proof-pq)




  fourGenCommutativityConnector : (r p s q : Fin n) 
                                  → (proof-rp : toℕ r < toℕ p) 
                                  → (proof-ps : toℕ p < toℕ s) 
                                  → (proof-sq : toℕ s < toℕ q) 
                                  → (proof-rq : toℕ r < toℕ q) 
                                  → (proof-pq : toℕ p < toℕ q) 
                                  → base ≡ base

      --           A p q
      --        b ­- - - > b
      --        ^         ^
      --   A r q|         |  sym (A s q)
      --        |         |
      --        b - - - > b
      --            Conn

  fourGenCommutativityComposition : (r p s q : Fin n) 
                                    → (proof-rp : toℕ r < toℕ p) 
                                    → (proof-ps : toℕ p < toℕ s) 
                                    → (proof-sq : toℕ s < toℕ q) 
                                    → (proof-rq : toℕ r < toℕ q) 
                                    → (proof-pq : toℕ p < toℕ q) 
                                    → Square
                                          (gen r q proof-rq)
                                          (sym (gen s q proof-sq))
                                          (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq proof-rq proof-pq )
                                          (gen p q proof-pq)

  fourGenCommutativity : (r p s q : Fin n) 
                                    → (proof-rp : toℕ r < toℕ p) 
                                    → (proof-ps : toℕ p < toℕ s) 
                                    → (proof-sq : toℕ s < toℕ q) 
                                    → (proof-rs : toℕ r < toℕ s) 
                                    → (proof-rq : toℕ r < toℕ q) 
                                    → (proof-pq : toℕ p < toℕ q) 
                                    → Square
                                          (gen r s proof-rs)
                                          (gen r s proof-rs)
                                          (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq proof-rq proof-pq)
                                          (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq proof-rq proof-pq)


GenComposer : {n : ℕ} (p q r s : Fin n) → (proof-pq : toℕ p < toℕ q) → (proof-rs : toℕ r < toℕ s)  → Path (BPureBraid n) base base
GenComposer p q r s proof-pq proof-rs = (gen p q proof-pq) ∙ (gen r s proof-rs)

CommonComposer : {n : ℕ} (r p q : Fin n) → (proof-rq : toℕ r < toℕ q) → (proof-pq : toℕ p < toℕ q) → Path (BPureBraid n) base base
CommonComposer r p q proof-rq proof-pq = GenComposer r q p q proof-rq proof-pq




addStrand : {n : ℕ} (b : BPureBraid n) → BPureBraid (suc n)
addStrand base = base
addStrand (gen p q proof-pq i) = gen (fsuc p) (fsuc q) (ssuc proof-pq) i
addStrand (twoGencommutativity1 p q r s proof-rs proof-sp proof-pq i j) = 
    twoGencommutativity1 (fsuc p) (fsuc q) (fsuc r) (fsuc s) (ssuc proof-rs) (ssuc proof-sp) (ssuc proof-pq) i j
addStrand (twoGencommutativity2 p q r s proof-pr proof-rs proof-sq proof-pq i j) = 
    twoGencommutativity2 (fsuc p) (fsuc q) (fsuc r) (fsuc s) (ssuc proof-pr) (ssuc proof-rs) (ssuc proof-sq) (ssuc proof-pq) i j

addStrand (threeGenCommutativityConnector r p q proof-rp proof-pq proof-rq i) = 
    threeGenCommutativityConnector (fsuc r) (fsuc p) (fsuc q) (ssuc proof-rp) (ssuc proof-pq) (ssuc proof-rq) i

addStrand (threeGenCommutativityLeft r p q proof-rp proof-pq proof-rq i j) = 
    threeGenCommutativityLeft (fsuc r) (fsuc p) (fsuc q) (ssuc proof-rp) (ssuc proof-pq) (ssuc proof-rq) i j

addStrand (threeGenCommutativityMiddle r p q proof-rp proof-pq proof-rq i j) = 
    threeGenCommutativityMiddle (fsuc r) (fsuc p) (fsuc q) (ssuc proof-rp) (ssuc proof-pq) (ssuc proof-rq) i j
    
addStrand (threeGenCommutativityRight r p q proof-rp proof-pq proof-rq i j) = 
    threeGenCommutativityRight (fsuc r) (fsuc p) (fsuc q) (ssuc proof-rp) (ssuc proof-pq) (ssuc proof-rq) i j

addStrand (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq proof-rq proof-pq i) = 
    fourGenCommutativityConnector (fsuc r) (fsuc p) (fsuc s) (fsuc q) (ssuc proof-rp) (ssuc proof-ps) (ssuc proof-sq) (ssuc proof-rq) (ssuc proof-pq) i

addStrand (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq proof-rq proof-pq i j) = 
    fourGenCommutativityComposition (fsuc r) (fsuc p) (fsuc s) (fsuc q) (ssuc proof-rp) (ssuc proof-ps) (ssuc proof-sq) (ssuc proof-rq) (ssuc proof-pq) i j

addStrand (fourGenCommutativity r p s q proof-rp proof-ps proof-sq proof-rs proof-rq proof-pq i j) = 
    fourGenCommutativity (fsuc r) (fsuc p) (fsuc s) (fsuc q) (ssuc proof-rp) (ssuc proof-ps) (ssuc proof-sq) (ssuc proof-rs) (ssuc proof-rq) (ssuc proof-pq) i j


delStrand : {n : ℕ} (b : BPureBraid (suc n)) → BPureBraid n
delStrand base = base

delStrand (gen (zero , proof-p) (q , proof-q) proof-pq i) = base
delStrand (gen (suc p , proof-p) (zero , proof-q) proof-pq i) = base
delStrand (gen (suc p , proof-p) (suc q , proof-q) proof-pq i) = gen ( p , pred proof-p) (q , pred proof-q) (pred proof-pq) i


-- Commutivity case 1 : r < s < p < q  ⇒ (gen p q ) · (gen r s) ≡ (gen r s) ∙ (gen p q)
-- these cases are absurd and will not be used
delStrand (twoGencommutativity1 (zero , proof-p) (zero , proof-q) (zero , proof-r) (zero , proof-s) proof-rs proof-sp proof-pq i j) = base
delStrand (twoGencommutativity1 (zero , proof-p) (zero , proof-q) (zero , proof-r) (suc s , proof-s) proof-rs proof-sp proof-pq i j) = base
delStrand (twoGencommutativity1 (zero , proof-p) (zero , proof-q) (suc r , proof-r) (zero , proof-s) proof-rs proof-sp proof-pq i j) =  base
delStrand (twoGencommutativity1 (suc p , proof-p) (zero , proof-q) (zero , proof-r) (zero , proof-s) proof-rs proof-sp proof-pq i j) =  base
delStrand (twoGencommutativity1 (suc p , proof-p) (zero , proof-q) (zero , proof-r) (suc s , proof-s) proof-rs proof-sp proof-pq i j) = base
delStrand (twoGencommutativity1 (suc p , proof-p) (zero , proof-q) (suc r , proof-r) (zero , proof-s) proof-rs proof-sp proof-pq i j) = base
delStrand (twoGencommutativity1 (zero , proof-p) (suc q , proof-q) (zero , proof-r) (zero , proof-s) proof-rs proof-sp proof-pq i j) = base
delStrand (twoGencommutativity1 (zero , proof-p) (suc q , proof-q) (zero , proof-r) (suc s , proof-s) proof-rs proof-sp proof-pq i j) = base
delStrand (twoGencommutativity1 (zero , proof-p) (suc q , proof-q) (suc r , proof-r) (zero , proof-s) proof-rs proof-sp proof-pq i j) = base

delStrand (twoGencommutativity1 (zero , proof-p) (zero , proof-q) (suc r , proof-r) (suc s , proof-s) proof-rs proof-sp proof-pq i j) = 
    gen (r , pred proof-r) (s , pred proof-s) (pred proof-rs) i

delStrand (twoGencommutativity1 (zero , proof-p) (suc q , proof-q) (suc r , proof-r) (suc s , proof-s) proof-rs proof-sp proof-pq i j) = 
    gen (r , pred proof-r) (s , pred proof-s) (pred proof-rs) i

delStrand (twoGencommutativity1 (suc p , proof-p) (zero , proof-q) (suc r , proof-r) (suc s , proof-s) proof-rs proof-sp proof-pq i j) = 
    gen (r , pred proof-r) (s , pred proof-s) (pred proof-rs) i

delStrand (twoGencommutativity1 (suc p , proof-p) (suc q , proof-q) (zero , proof-r) (zero , proof-s) proof-rs proof-sp proof-pq i j) =  
    gen (p , pred proof-p) (q , pred proof-q) (pred proof-pq) j

delStrand (twoGencommutativity1 (suc p , proof-p) (suc q , proof-q) (suc r , proof-r) (zero , proof-s) proof-rs proof-sp proof-pq i j) =  
    gen (p , pred proof-p) (q , pred proof-q) (pred proof-pq) j
    

-- only two cases that are possible, either r is zero or it is not
delStrand (twoGencommutativity1 (suc p , proof-p) (suc q , proof-q) (zero , proof-r) (suc s , proof-s) proof-rs proof-sp proof-pq i j) = 
    gen (p , pred proof-p) (q , pred proof-q) (pred proof-pq) j
    
delStrand (twoGencommutativity1 (suc p , proof-p) (suc q , proof-q) (suc r , proof-r) (suc s , proof-s) proof-rs proof-sp proof-pq i j) = 
    twoGencommutativity1 (p , pred proof-p) (q , pred proof-q) (r , pred proof-r) (s , pred proof-s) (pred proof-rs) (pred proof-sp) (pred proof-pq) i j




-- Commutivity case 2 : p < r < s < q ⇒ (gen p q ) · (gen r s) ≡ (gen r s) ∙ (gen p q)
-- these cases are impossible
delStrand (twoGencommutativity2 (zero , proof-p) (zero , proof-q) (zero , proof-r) (zero , proof-s) proof-pr proof-rs proof-sq proof-pq i j) = base
delStrand (twoGencommutativity2 (zero , proof-p) (zero , proof-q) (zero , proof-r) (suc s , proof-s) proof-pr proof-rs proof-sq proof-pq i j) = base
delStrand (twoGencommutativity2 (zero , proof-p) (zero , proof-q) (suc r , proof-r) (zero , proof-s) proof-pr proof-rs proof-sq proof-pq i j) = base
delStrand (twoGencommutativity2 (zero , proof-p) (suc q , proof-q) (zero , proof-r) (zero , proof-s) proof-pr proof-rs proof-sq proof-pq i j) = base
delStrand (twoGencommutativity2 (zero , proof-p) (suc q , proof-q) (zero , proof-r) (suc s , proof-s) proof-pr proof-rs proof-sq proof-pq i j) = base
delStrand (twoGencommutativity2 (zero , proof-p) (suc q , proof-q) (suc r , proof-r) (zero , proof-s) proof-pr proof-rs proof-sq proof-pq i j) = base
delStrand (twoGencommutativity2 (suc p , proof-p) (zero , proof-q) (zero , proof-r) (zero , proof-s) proof-pr proof-rs proof-sq proof-pq i j) = base
delStrand (twoGencommutativity2 (suc p , proof-p) (zero , proof-q) (zero , proof-r) (suc s , proof-s) proof-pr proof-rs proof-sq proof-pq i j) = base
delStrand (twoGencommutativity2 (suc p , proof-p) (zero , proof-q) (suc r , proof-r) (zero , proof-s) proof-pr proof-rs proof-sq proof-pq i j) = base

delStrand (twoGencommutativity2 (zero , proof-p) (zero , proof-q) (suc r , proof-r) (suc s , proof-s) proof-pr proof-rs proof-sq proof-pq i j) = 
    gen (r , pred proof-r) (s , pred proof-s) (pred proof-rs) i

delStrand (twoGencommutativity2 (suc p , proof-p) (zero , proof-q) (suc r , proof-r) (suc s , proof-s) proof-pr proof-rs proof-sq proof-pq i j) = 
    gen (r , pred proof-r) (s , pred proof-s) (pred proof-rs) i

delStrand (twoGencommutativity2 (suc p , proof-p) (suc q , proof-q) (zero , proof-r) (zero , proof-s) proof-pr proof-rs proof-sq proof-pq i j) = 
    gen (p , pred proof-p) (q , pred proof-q) (pred proof-pq) j

delStrand (twoGencommutativity2 (suc p , proof-p) (suc q , proof-q) (zero , proof-r) (suc s , proof-s) proof-pr proof-rs proof-sq proof-pq i j) =
    gen (p , pred proof-p) (q , pred proof-q) (pred proof-pq) j

delStrand (twoGencommutativity2 (suc p , proof-p) (suc q , proof-q) (suc r , proof-r) (zero , proof-s) proof-pr proof-rs proof-sq proof-pq i j) =
    gen (p , pred proof-p) (q , pred proof-q) (pred proof-pq) j


-- only two cases are possible, p = 0 or p != 0 and r s q > 0
delStrand (twoGencommutativity2 (zero , proof-p) (suc q , proof-q) (suc r , proof-r) (suc s , proof-s) proof-pr proof-rs proof-sq proof-pq i j) = 
    gen (r , pred proof-r) (s , pred proof-s) (pred proof-rs) i

delStrand (twoGencommutativity2 (suc p , proof-p) (suc q , proof-q) (suc r , proof-r) (suc s , proof-s) proof-pr proof-rs proof-sq proof-pq i j) = 
    twoGencommutativity2 (p , pred proof-p) (q , pred proof-q) (r , pred proof-r) (s , pred proof-s) (pred proof-pr) (pred proof-rs) (pred proof-sq) (pred proof-pq) i j




-- r < p < q
-- impossible cases
delStrand (threeGenCommutativityConnector (zero , proof-r) (zero , proof-p) (zero , proof-q) proof-rp proof-pq proof-rq i) = base
delStrand (threeGenCommutativityConnector (zero , proof-r) (zero , proof-p) (suc q , proof-q) proof-rp proof-pq proof-rq i) = base
delStrand (threeGenCommutativityConnector (zero , proof-r) (suc p , proof-p) (zero , proof-q) proof-rp proof-pq proof-rq i) = base
delStrand (threeGenCommutativityConnector (suc r , proof-r) (zero , proof-p) (zero , proof-q) proof-rp proof-pq proof-rq i) = base

delStrand (threeGenCommutativityConnector (suc r , proof-r) (zero , proof-p) (suc q , proof-q) proof-rp proof-pq proof-rq i) = 
    gen (r , pred proof-r) (q , pred proof-q) (pred proof-rq) i
    
delStrand (threeGenCommutativityConnector (suc r , proof-r) (suc p , proof-p) (zero , proof-q) proof-rp proof-pq proof-rq i) = 
    gen  (r , pred proof-r) (p , pred proof-p) (pred proof-rp) i


-- only possibele cases
delStrand (threeGenCommutativityConnector (zero , proof-r) (suc p , proof-p) (suc q , proof-q) proof-rp proof-pq proof-rq i) = 
    gen (p , pred proof-p) (q , pred proof-q) (pred proof-pq) i

delStrand (threeGenCommutativityConnector (suc r , proof-r) (suc p , proof-p) (suc q , proof-q) proof-rp proof-pq proof-rq i) = 
    threeGenCommutativityConnector (r , pred proof-r) (p , pred proof-p) (q , pred proof-q) (pred proof-rp) (pred proof-pq) (pred proof-rq) i



-- if p or q = 0, then absurd case as no natural number r such that r < 0

--impossible case
delStrand (threeGenCommutativityLeft (zero , proof-r) (zero , proof-p) (zero , proof-q) proof-rp proof-pq proof-rq i j) = base
delStrand (threeGenCommutativityLeft (zero , proof-r) (zero , proof-p) (suc q , proof-q) proof-rp proof-pq proof-rq i j) = base
delStrand (threeGenCommutativityLeft (zero , proof-r) (suc p , proof-p) (zero , proof-q) proof-rp proof-pq proof-rq i j) = base
delStrand (threeGenCommutativityLeft (suc r , proof-r) (zero , proof-p) (zero , proof-q) proof-rp proof-pq proof-rq i j) = base

delStrand (threeGenCommutativityLeft (suc r , proof-r) (zero , proof-p) (suc q , proof-q) proof-rp proof-pq proof-rq i j) = 
    gen (r , pred proof-r)  (q , pred proof-q) (pred proof-rq) (i ∧ ~ j)
delStrand (threeGenCommutativityLeft (suc r , proof-r) (suc p , proof-p) (zero , proof-q) proof-rp proof-pq proof-rq i j) = 
    gen  (r , pred proof-r) (p , pred proof-p) (pred proof-rp)  i


-- only cases that are possible
delStrand (threeGenCommutativityLeft (zero , proof-r) (suc p , proof-p) (suc q , proof-q) proof-rp proof-pq proof-rq i j) = 
    gen (p , pred proof-p) (q , pred proof-q) (pred proof-pq) ( i ∨ j  )
delStrand (threeGenCommutativityLeft (suc r , proof-r) (suc p , proof-p) (suc q , proof-q) proof-rp proof-pq proof-rq i j) = 
    threeGenCommutativityLeft (r , pred proof-r) (p , pred proof-p) (q , pred proof-q) (pred proof-rp) (pred proof-pq) (pred proof-rq) i j



-- impossible case
delStrand (threeGenCommutativityMiddle (zero , proof-r) (zero , proof-p) (zero , proof-q) proof-rp proof-pq proof-rq i j) = base
delStrand (threeGenCommutativityMiddle (zero , proof-r) (zero , proof-p) (suc q , proof-q) proof-rp proof-pq proof-rq i j) = base
delStrand (threeGenCommutativityMiddle (zero , proof-r) (suc p , proof-p) (zero , proof-q) proof-rp proof-pq proof-rq i j) = base
delStrand (threeGenCommutativityMiddle (suc r , proof-r) (zero , proof-p) (zero , proof-q) proof-rp proof-pq proof-rq i j) = base

delStrand (threeGenCommutativityMiddle (suc r , proof-r) (zero , proof-p) (suc q , proof-q) proof-rp proof-pq proof-rq i j) = 
    gen (r , pred proof-r)  (q , pred proof-q) (pred proof-rq)  i

delStrand (threeGenCommutativityMiddle (suc r , proof-r) (suc p , proof-p) (zero , proof-q) proof-rp proof-pq proof-rq i j) = 
    gen  (r , pred proof-r) (p , pred proof-p) (pred proof-rp) ( i ∨ j  )


-- only cases that are possible
delStrand (threeGenCommutativityMiddle (zero , proof-r) (suc p , proof-p) (suc q , proof-q) proof-rp proof-pq proof-rq i j) = 
    gen (p , pred proof-p) (q , pred proof-q) (pred proof-pq) ( i ∧ ~ j  )

delStrand (threeGenCommutativityMiddle (suc r , proof-r) (suc p , proof-p) (suc q , proof-q) proof-rp proof-pq proof-rq i j) = 
    threeGenCommutativityMiddle (r , pred proof-r) (p , pred proof-p) (q , pred proof-q) (pred proof-rp) (pred proof-pq) (pred proof-rq) i j



delStrand (threeGenCommutativityRight (zero , proof-r) (zero , proof-p) (zero , proof-q) proof-rp proof-pq proof-rq i j) = base
delStrand (threeGenCommutativityRight (zero , proof-r) (zero , proof-p) (suc q , proof-q) proof-rp proof-pq proof-rq i j) = base
delStrand (threeGenCommutativityRight (zero , proof-r) (suc p , proof-p) (zero , proof-q) proof-rp proof-pq proof-rq i j) = base
delStrand (threeGenCommutativityRight (suc r , proof-r) (zero , proof-p) (zero , proof-q) proof-rp proof-pq proof-rq i j) = base

delStrand (threeGenCommutativityRight (suc r , proof-r) (zero , proof-p) (suc q , proof-q) proof-rp proof-pq proof-rq i j)  = 
    gen (r , pred proof-r)  (q , pred proof-q) (pred proof-rq) (  i ∨ j )

delStrand (threeGenCommutativityRight (suc r , proof-r) (suc p , proof-p) (zero , proof-q) proof-rp proof-pq proof-rq i j)  =
     gen  (r , pred proof-r) (p , pred proof-p) (pred proof-rp) ( i ∧ ~ j  )

delStrand (threeGenCommutativityRight (zero , proof-r) (suc p , proof-p) (suc q , proof-q) proof-rp proof-pq proof-rq i j)  =
     gen (p , pred proof-p) (q , pred proof-q) (pred proof-pq)  i
     
delStrand (threeGenCommutativityRight (suc r , proof-r) (suc p , proof-p) (suc q , proof-q) proof-rp proof-pq proof-rq i j) = 
    threeGenCommutativityRight (r , pred proof-r) (p , pred proof-p) (q , pred proof-q) (pred proof-rp) (pred proof-pq) (pred proof-rq) i j




--impossible cases
delStrand (fourGenCommutativityConnector (zero , proof-r) (zero , proof-p) (zero , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i) = base
delStrand (fourGenCommutativityConnector (zero , proof-r) (zero , proof-p) (zero , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i) = base
delStrand (fourGenCommutativityConnector (zero , proof-r) (zero , proof-p) (suc s , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i) = base
delStrand (fourGenCommutativityConnector (zero , proof-r) (suc p , proof-p) (zero , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i) = base
delStrand (fourGenCommutativityConnector (zero , proof-r) (suc p , proof-p) (suc s , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i) = base
delStrand (fourGenCommutativityConnector (suc r , proof-r) (zero , proof-p) (zero , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i) = base
delStrand (fourGenCommutativityConnector (suc r , proof-r) (zero , proof-p) (suc s , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i) = base
delStrand (fourGenCommutativityConnector (suc r , proof-r) (suc p , proof-p) (zero , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i) = base
delStrand (fourGenCommutativityConnector (suc r , proof-r) (suc p , proof-p) (suc s , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i) = base

delStrand (fourGenCommutativityConnector (suc r , proof-r) (zero , proof-p) (suc s , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i) = 
    CommonComposer (r , pred proof-r) (s , pred proof-s) (q , pred proof-q) (pred proof-rq) (pred proof-sq) i

delStrand (fourGenCommutativityConnector (suc r , proof-r) (suc p , proof-p) (zero , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i) =  
    CommonComposer (r , pred proof-r) (p , pred proof-p) (q , pred proof-q) (pred proof-rq) (pred proof-pq) i

delStrand (fourGenCommutativityConnector (zero , proof-r) (zero , proof-p) (suc s , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i) = 
    gen (s , pred proof-s) (q , pred proof-q) (pred proof-sq) i

delStrand (fourGenCommutativityConnector (zero , proof-r) (suc p , proof-p) (zero , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i) =
    gen (p , pred proof-p) (q , pred proof-q) (pred proof-pq) i

delStrand (fourGenCommutativityConnector (suc r , proof-r) (zero , proof-p) (zero , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i) = 
    gen (r , pred proof-r) (q , pred proof-q) (pred proof-rq) i

--possible cases
delStrand (fourGenCommutativityConnector (zero , proof-r) (suc p , proof-p) (suc s , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i) =
    CommonComposer (p , pred proof-p) (s , pred proof-s) (q , pred proof-q) (pred proof-pq) (pred proof-sq) i

delStrand (fourGenCommutativityConnector (suc r , proof-r) (suc p , proof-p) (suc s , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i) =
  fourGenCommutativityConnector 
  (r , pred proof-r) (p , pred proof-p) (s , pred proof-s) (q , pred proof-q)
  (pred proof-rp) (pred proof-ps) (pred proof-sq) (pred proof-rq) (pred proof-pq) i


--impossible cases
delStrand (fourGenCommutativityComposition (zero , proof-r) (zero , proof-p) (zero , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i j) = base
delStrand (fourGenCommutativityComposition (zero , proof-r) (zero , proof-p) (zero , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i j) = base
delStrand (fourGenCommutativityComposition (zero , proof-r) (zero , proof-p) (suc s , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i j) = base
delStrand (fourGenCommutativityComposition (zero , proof-r) (suc p , proof-p) (zero , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i j) = base
delStrand (fourGenCommutativityComposition (zero , proof-r) (suc p , proof-p) (suc s , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i j) = base
delStrand (fourGenCommutativityComposition (suc r , proof-r) (zero , proof-p) (zero , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i j) = base
delStrand (fourGenCommutativityComposition (suc r , proof-r) (zero , proof-p) (suc s , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i j) = base
delStrand (fourGenCommutativityComposition (suc r , proof-r) (suc p , proof-p) (zero , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i j) = base
delStrand (fourGenCommutativityComposition (suc r , proof-r) (suc p , proof-p) (suc s , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i j) = base


-- generators only exist if strand q isnt deleted
delStrand (fourGenCommutativityComposition (zero , proof-r) (zero , proof-p) (suc s , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i j) = 
    gen (s , pred proof-s) (q , pred proof-q) (pred proof-sq) (i ∧ ( ~ j))

delStrand (fourGenCommutativityComposition (zero , proof-r) (suc p , proof-p) (zero , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i j) = 
    gen (p , pred proof-p) (q , pred proof-q) (pred proof-pq) i

delStrand (fourGenCommutativityComposition (suc r , proof-r) (zero , proof-p) (zero , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i j) = 
    gen (r , pred proof-r) (q , pred proof-q) (pred proof-rq) (i ∨ j)


delStrand (fourGenCommutativityComposition (suc r , proof-r) (zero , proof-p) (suc s , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i j) = 
    ⊥.rec {A = Square 
                (gen (r , pred proof-r) (q , pred proof-q) (pred proof-rq))
                (sym (gen (s , pred proof-s) (q , pred proof-q) (pred proof-sq)))
                (CommonComposer (r , pred proof-r) (s , pred proof-s)
                (q , pred proof-q) (pred proof-rq) (pred proof-sq))
                refl }
            (!<0 proof-rp) i j

delStrand (fourGenCommutativityComposition (suc r , proof-r) (suc p , proof-p) (zero , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i j) = 
    ⊥.rec {A = Square
                (gen (r , pred proof-r) (q , pred proof-q) (pred proof-rq))
                refl 
                (CommonComposer (r , pred proof-r) (p , pred proof-p)
                (q , pred proof-q) (pred proof-rq) (pred proof-pq))
                (gen (p , pred proof-p) (q , pred proof-q) (pred proof-pq)) }
        (!<0 proof-ps) i j 



-- possible cases
delStrand (fourGenCommutativityComposition (zero , proof-r) (suc p , proof-p) (suc s , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i j) =
    compPath-filler 
      (gen (p , pred proof-p) (q , pred proof-q) (pred proof-pq))
      (gen (s , pred proof-s) (q , pred proof-q) (pred proof-sq)) (~ j) i


delStrand (fourGenCommutativityComposition (suc r , proof-r) (suc p , proof-p) (suc s , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rq proof-pq i j) = 
    fourGenCommutativityComposition 
      (r , pred proof-r) (p , pred proof-p) (s , pred proof-s) (q , pred proof-q) 
      (pred proof-rp) (pred proof-ps) (pred proof-sq) (pred proof-rq) (pred proof-pq) i j
    



--impossible case

delStrand (fourGenCommutativity (zero , proof-r) (zero , proof-p) (zero , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rs proof-rq proof-pq i j) = base
delStrand (fourGenCommutativity (zero , proof-r) (zero , proof-p) (zero , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rs proof-rq proof-pq i j) = base
delStrand (fourGenCommutativity (zero , proof-r) (zero , proof-p) (suc s , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rs proof-rq proof-pq i j) = base
delStrand (fourGenCommutativity (zero , proof-r) (suc p , proof-p) (zero , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rs proof-rq proof-pq i j) = base
delStrand (fourGenCommutativity (suc r , proof-r) (suc p , proof-p) (zero , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rs proof-rq proof-pq i j) = base
delStrand (fourGenCommutativity (zero , proof-r) (suc p , proof-p) (suc s , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rs proof-rq proof-pq i j) = base
delStrand (fourGenCommutativity (suc r , proof-r) (zero , proof-p) (zero , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rs proof-rq proof-pq i j) = base

delStrand (fourGenCommutativity (suc r , proof-r) (suc p , proof-p) (zero , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rs proof-rq proof-pq i j) = 
    CommonComposer (r , pred proof-r) (p , pred proof-p)
         (q , pred proof-q) (pred proof-rq) (pred proof-pq) i

delStrand (fourGenCommutativity (zero , proof-r) (suc p , proof-p) (zero , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rs proof-rq proof-pq i j)  = 
    gen (p , pred proof-p) (q , pred proof-q) (pred proof-pq) i

delStrand (fourGenCommutativity (suc r , proof-r) (zero , proof-p) (zero , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rs proof-rq proof-pq i j)  = 
    gen (r , pred proof-r) (q , pred proof-q) (pred proof-rq) i

delStrand (fourGenCommutativity (suc r , proof-r) (zero , proof-p) (suc s , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rs proof-rq proof-pq i j)  = 
    gen (r , pred proof-r) (s , pred proof-s) (pred proof-rs) j
    
delStrand (fourGenCommutativity (suc r , proof-r) (zero , proof-p) (suc s , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rs proof-rq proof-pq i j) =
     ⊥.rec {A = Square 
                    (gen (r , pred proof-r) (s , pred proof-s) (pred proof-rs)) 
                    (gen (r , pred proof-r) (s , pred proof-s) (pred proof-rs))
                    (CommonComposer (r , pred proof-r) (s , pred proof-s)
                    (q , pred proof-q) (pred proof-rq) (pred proof-sq))
                    (CommonComposer (r , pred proof-r) (s , pred proof-s)
                    (q , pred proof-q) (pred proof-rq) (pred proof-sq))
                }
                (!<0 proof-rp) i  j

delStrand (fourGenCommutativity (zero , proof-r) (zero , proof-p) (suc s , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rs proof-rq proof-pq i j)  = 
    gen (s ,  pred proof-s) (q ,  pred proof-q) ( pred proof-sq)  i
delStrand (fourGenCommutativity (suc r , proof-r) (suc p , proof-p) (suc s , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq proof-rs proof-rq proof-pq i j) = 
    gen (r , pred proof-r) (s , pred proof-s) (pred proof-rs) j



-- possible cases
delStrand {n = n} (fourGenCommutativity (zero , proof-r) (suc p , proof-p) (suc s , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rs proof-rq proof-pq i j) = 
    CommonComposer (p , pred proof-p) (s , pred proof-s) (q , pred proof-q) (pred proof-pq) (pred proof-sq) i

-- fourGenCommutativityConnector (zero , {! zero-≤ {n = n}  !}) (p , pred proof-p) (s , pred proof-s) (q , pred proof-q) {!  !} (pred proof-ps) (pred proof-sq) i
delStrand (fourGenCommutativity (suc r , proof-r) (suc p , proof-p) (suc s , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq proof-rs proof-rq proof-pq i j) = 
    fourGenCommutativity 
    (r , pred proof-r) (p , pred proof-p) (s , pred proof-s) (q , pred proof-q) 
    (pred proof-rp) (pred  proof-ps) (pred  proof-sq) (pred proof-rs) (pred proof-rq) (pred proof-pq) i j



 