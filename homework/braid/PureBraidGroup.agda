{-# OPTIONS --safe #-}


module homework.braid.PureBraidGroup where
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat.Base
open import Cubical.Data.Fin.Base
open import Cubical.Data.Nat.Order 
open import Cubical.Data.Empty as ⊥


-- data B3 : Type where
--   base  : B3
--   generator1 : base ≡ base
--   generator2 : base ≡ base
--   relation : Square generator1 generator1 generator2 generator2
--   makeGroupoid : {x y : B3} → isSet (x ≡ y)
  


data BPureBraid (n : ℕ) : Type where -- the space whose loops are the pure braid group of n strands
  base : BPureBraid n
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

  threewayCommutativityCommon : (r p q : Fin n) → (proof-rp : toℕ r < toℕ p) → (proof-pq : toℕ p < toℕ q) → base ≡ base

  threewayCommutativityLeft : (r p q : Fin n) → (proof-rp : toℕ r < toℕ p) → (proof-pq : toℕ p < toℕ q) → Square
                                                                                                           (gen r p proof-rp)
                                                                                                           (threewayCommutativityCommon r p q proof-rp proof-pq)
                                                                                                           (sym (gen p q proof-pq))
                                                                                                           (gen r q (<-trans proof-rp proof-pq)) 

                                                                                            
  threewayCommutativityRight : (r p q : Fin n) → (proof-rp : toℕ r < toℕ p) → (proof-pq : toℕ p < toℕ q) → Square 
                                                                                                            ((threewayCommutativityCommon r p q proof-rp proof-pq)) 
                                                                                                            (gen p q proof-pq) 
                                                                                                            (gen r q (<-trans proof-rp proof-pq)) 
                                                                                                            (sym (gen r p proof-rp))
                                                                                                            
  threewayCommutativityTop : (r p q : Fin n) → (proof-rp : toℕ r < toℕ p) → (proof-pq : toℕ p < toℕ q) → Square 
                                                                                                            (gen r p proof-rp)
                                                                                                            (sym (gen p q proof-pq))
                                                                                                            ((threewayCommutativityCommon r p q proof-rp proof-pq)) 
                                                                                                            (gen r q (<-trans proof-rp proof-pq)) 
                                                                                                            
  associativityLeft : (r p s q : Fin n) → (proof-rp : toℕ r < toℕ p) → (proof-ps : toℕ p < toℕ s) → (proof-sq : toℕ s < toℕ q) → Square (gen r q (<-trans (<-trans proof-rp proof-ps  ) proof-sq))
                                                                                                                                        (gen p q (<-trans proof-ps proof-sq))
                                                                                                                                        (gen r s (<-trans proof-rp proof-ps))
                                                                                                                                        (sym (gen s q proof-sq))
                                                                                                                                        
  associativityRight : (r p s q : Fin n) → (proof-rp : toℕ r < toℕ p) → (proof-ps : toℕ p < toℕ s) → (proof-sq : toℕ s < toℕ q) → Square (gen r q (<-trans (<-trans proof-rp proof-ps  ) proof-sq))
                                                                                                                                        (gen p q (<-trans proof-ps proof-sq))
                                                                                                                                        (gen r s (<-trans proof-rp proof-ps))
                                                                                                                                        (sym (gen s q proof-sq))
                                                                                                                                        
  associativityConnector : (r p s q : Fin n) → (proof-rp : toℕ r < toℕ p) → (proof-ps : toℕ p < toℕ s) → (proof-sq : toℕ s < toℕ q) → (associativityRight r p s q proof-rp proof-ps proof-sq) ≡ ( associativityLeft r p s q proof-rp proof-ps proof-sq)





addGen : {n : ℕ} (b : BPureBraid n) → BPureBraid (suc n)
addGen base = base
addGen (gen (m , proof-m) (n , proof-n) constraint i) = gen (m , ≤-suc proof-m) (n , ≤-suc proof-n) constraint i
addGen (commutativity1 (p , proof-p) (q , proof-q) (r , proof-r) (s , proof-s) proof-rs proof-sp proof-pq i j) = commutativity1 (p , ≤-suc proof-p) (q , ≤-suc proof-q) (r , ≤-suc proof-r) (s , ≤-suc proof-s) proof-rs proof-sp proof-pq i j
addGen (commutativity2 (p , proof-p) (q , proof-q) (r , proof-r) (s , proof-s) proof-pr proof-rs proof-sq proof-pq i j) = {!   !} --commutativity2 (p , ≤-suc proof-p ) ( q , ≤-suc proof-q) (r , ≤-suc proof-r) (s , ≤-suc proof-s) proof-pr  proof-rs  proof-sq i j


addGen (threewayCommutativityCommon (r , proof-r) (p , proof-p) (q , proof-q) proof-rp proof-pq i)  = threewayCommutativityCommon ( r , ≤-suc proof-r) (p , ≤-suc proof-p) (q , ≤-suc proof-q) proof-rp proof-pq i 
addGen (threewayCommutativityLeft (r , proof-r) (p , proof-p) (q , proof-q)  proof-rp proof-pq i j) = threewayCommutativityLeft (r , ≤-suc proof-r) (p , ≤-suc proof-p) (q , ≤-suc proof-q) proof-rp proof-pq i j 
addGen (threewayCommutativityRight (r , proof-r) (p , proof-p) (q , proof-q) proof-rp proof-pq i j) = threewayCommutativityRight (r , ≤-suc proof-r) (p , ≤-suc proof-p) (q , ≤-suc proof-q) proof-rp proof-pq i j
addGen (threewayCommutativityTop (r , proof-r) (p , proof-p) (q , proof-q)  proof-rp proof-pq i j)  =  threewayCommutativityTop (r , ≤-suc proof-r) (p , ≤-suc proof-p) (q , ≤-suc proof-q) proof-rp proof-pq i j

addGen (associativityLeft (r , proof-r) (p , proof-p) (s , proof-s) (q , proof-q) proof-rp proof-ps proof-sq i j) = associativityLeft (r , ≤-suc proof-r) (p , ≤-suc proof-p) (s , ≤-suc proof-s) (q , ≤-suc proof-q) proof-rp proof-ps proof-sq i j
addGen (associativityRight (r , proof-r) (p , proof-p) (s , proof-s) (q , proof-q) proof-rp proof-ps proof-sq i j) = associativityRight (r , ≤-suc proof-r) (p , ≤-suc proof-p) (s , ≤-suc proof-s) (q , ≤-suc proof-q) proof-rp proof-ps proof-sq i j
addGen (associativityConnector (r , proof-r) (p , proof-p) (s , proof-s) (q , proof-q) proof-rp proof-ps proof-sq i j k) = associativityConnector  (r , ≤-suc proof-r) (p , ≤-suc proof-p) (s , ≤-suc proof-s) (q , ≤-suc proof-q) proof-rp proof-ps proof-sq i j k                                                                                             
                                                                                                        


deletion : {n : ℕ} (b : BPureBraid (suc n)) → BPureBraid n
deletion base = base

deletion (gen (zero , proof-p) (q , proof-q) constraint i) = base 
deletion (gen (suc p , proof-p) (zero , proof-q) constraint i) = base
deletion (gen (suc p , proof-p) (suc q , proof-q) constraint i) = gen ( p , pred-≤-pred proof-p) (q , pred-≤-pred proof-q) (pred-≤-pred constraint) i


deletion (commutativity1 (zero , proof-p) (q , proof-q) (r , proof-r ) (s , proof-s) proof-rs proof-sp proof-pq i j) = ⊥.rec  {A = Square  (gen (zero , ?) (q , ?) ?) {!   !} {!   !} {!   !}}  (¬-<-zero proof-sp) i j 
deletion (commutativity1 (suc p , proof-p) (zero , proof-q) r s proof-rs proof-sp proof-pq i j) = ⊥.rec {A = Square {!   !} {!   !} {!   !} {!   !}} (¬-<-zero proof-pq) i j 
deletion (commutativity1 (suc p , proof-p) (suc q , proof-q) r (zero , proof-s) proof-rs proof-sp proof-pq i j) = ⊥.rec {A = Square {!   !} {!   !} {!   !} {!   !}} (¬-<-zero proof-rs) i j 


deletion (commutativity1 (suc p , proof-p) (suc q , proof-q) (zero , proof-r) (suc s , proof-s) proof-rs proof-sp proof-pq i j) = gen (p , pred-≤-pred proof-p) (q , pred-≤-pred proof-q) (pred-≤-pred proof-pq) j
deletion (commutativity1 (suc p , proof-p) (suc q , proof-q) (suc r , proof-r) (suc s , proof-s) proof-rs proof-sp proof-pq i j) = commutativity1 (p , pred-≤-pred proof-p) (q , pred-≤-pred proof-q) (r , pred-≤-pred proof-r) (s , pred-≤-pred proof-s) (pred-≤-pred proof-rs) (pred-≤-pred proof-sp) (pred-≤-pred proof-pq) i j


deletion (commutativity2 p (zero , proof-q) r s proof-pr proof-rs proof-sq proof-pq i j) = ⊥.rec {A = Square {!   !} {!   !} {!   !} {!   !}} (¬-<-zero proof-sq) i j 
deletion (commutativity2 p (suc q , proof-q) (zero , proof-r) s proof-pr proof-rs proof-sq proof-pq i j) = ⊥.rec {A = Square {!   !} {!   !} {!   !} {!   !}} (¬-<-zero proof-pr) i j  
deletion (commutativity2 p (suc q , proof-q) (suc r , proof-r) (zero , proof-s) proof-pr proof-rs proof-sq proof-pq i j) = ⊥.rec {A = Square {!   !} {!   !} {!   !} {!   !}} (¬-<-zero proof-rs) i j 
deletion (commutativity2 (zero , proof-p) (suc q , proof-q) (suc r , proof-r) (suc s , proof-s) proof-pr proof-rs proof-sq proof-pq i j) = gen (r , pred-≤-pred proof-r) (s , pred-≤-pred proof-s) (pred-≤-pred proof-rs) i
deletion (commutativity2 (suc p , proof-p) (suc q , proof-q) (suc r , proof-r) (suc s , proof-s) proof-pr proof-rs proof-sq proof-pq i j) = commutativity2 (p , pred-≤-pred proof-p) (q , pred-≤-pred proof-q) (r , pred-≤-pred proof-r) (s , pred-≤-pred proof-s) (pred-≤-pred proof-pr) (pred-≤-pred  proof-rs) (pred-≤-pred  proof-sq) (pred-≤-pred  proof-pq) i j


deletion (threewayCommutativityCommon r p q proof-rp proof-pq i) = {!!}
deletion (threewayCommutativityLeft r p q proof-rp proof-pq i j) = {!!}
deletion (threewayCommutativityRight r p q proof-rp proof-pq i j) = {!!}
deletion (threewayCommutativityTop r p q proof-rp proof-pq i j) = {!!}


deletion (associativityLeft r p s q proof-rp proof-ps proof-sq i j) = {!!}
deletion (associativityRight r p s q proof-rp proof-ps proof-sq i j) = {!!}
deletion (associativityConnector r p s q proof-rp proof-ps proof-sq i j k) = {!!}
 