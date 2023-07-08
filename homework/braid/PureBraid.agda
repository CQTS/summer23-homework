{-# OPTIONS --safe #-}


module homework.braid.PureBraid where
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat.Base
open import Cubical.Data.Fin.Base
open import Cubical.Data.Nat.Order 



-- data B3 : Type where
--   base  : B3
--   generator1 : base ≡ base
--   generator2 : base ≡ base
--   relation : Square generator1 generator1 generator2 generator2
--   makeGroupoid : {x y : B3} → isSet (x ≡ y)
  


data BPureBraid (n : ℕ) : Type where -- the space whose loops are the pure braid group of n generators or n+1 strands
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
                          →  Square (gen p q (<-trans ( proof-pr) (<-trans proof-rs proof-sq)))  (gen p q ((<-trans ( proof-pr) (<-trans proof-rs proof-sq)))) (gen r s proof-rs) (gen r s proof-rs)
  



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
                                                                                                            


                                                                                                             
                                                                                                            
                                                                                                        



    
 


 