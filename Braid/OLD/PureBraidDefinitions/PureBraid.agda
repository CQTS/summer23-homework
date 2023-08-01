{-# OPTIONS --safe #-}
module Braid.OLD.PureBraidDefinitions.PureBraid where
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat.Base
open import Cubical.Data.Fin.Base
open import Cubical.Data.Nat.Order renaming (pred-≤-pred to pred ; suc-≤-suc to sucP)
open import Cubical.Data.Empty as ⊥


-- finpred-≤-pred : {n : ℕ} (f : Fin (suc (suc n))) → Fin (suc n)
-- finpred-≤-pred {n = n} (zero , proof) = fzero
-- finpred-≤-pred (suc p , proof) = p , pred proof



data BPureBraid (n : ℕ) :  Type where -- pure braid group of n strands
  base : BPureBraid n
  gen  : (p q : Fin n)  → base ≡ base
  identity : (p : Fin n) → Square (gen p p) refl refl refl
  genEquality : (p q : Fin n) → Square (gen p q) (gen q p) refl refl

  twoGenCommutativity1 : (p q r s : Fin n) 
                          → (proof-rp : toℕ r < toℕ p)
                          → ( proof-sp : toℕ s < toℕ p)
                          → ( proof-rq : toℕ r < toℕ q)
                          → ( proof-sq : toℕ s < toℕ q)
                          →  Square (gen p q)  (gen p q) (gen r s ) (gen r s)

  twoGenCommutativity2 : (p q r s : Fin n) → (proof-pr : toℕ p < toℕ r)
                          → ( proof-ps : toℕ p < toℕ s)
                          → ( proof-rq : toℕ r < toℕ q)
                          → (proof-sq : toℕ s < toℕ q)
                          → Square (gen p q) (gen p q) (gen r s) (gen r s)



  threeGenCommutativityConnector : (r p q : Fin n) → base ≡ base

                                                                            
  threeGenCommutativityComposition : (r p q : Fin n)
                                    → (proof-rp : toℕ r < toℕ p)
                                    → (proof-pq : toℕ p < toℕ q) 
                                    → Square 
                                            (gen p q )
                                            (sym (gen r q)) 
                                            (threeGenCommutativityConnector r p q)
                                            (gen r p)

  threeGenCommutativity : (r p q : Fin n)
                                    → (proof-rp : toℕ r < toℕ p)
                                    → (proof-pq : toℕ p < toℕ q) 
                                    → Square
                                            (threeGenCommutativityConnector r p q) 
                                            (threeGenCommutativityConnector q r p) 
                                            refl
                                            refl


  fourGenCommutativityConnector : (r p s q : Fin n)  → base ≡ base

  fourGenCommutativityComposition : (r p s q : Fin n) 
                                    → (proof-rp : toℕ r < toℕ p)
                                    → (proof-ps : toℕ p < toℕ s)
                                    → (proof-sq : toℕ s < toℕ q) 
                                    → Square
                                            (gen r q )
                                            (sym (gen s q))
                                            (fourGenCommutativityConnector r p s q)
                                            (gen p q )

  fourGenCommutativity :    (r p s q : Fin n) 
                            → (proof-rp : toℕ r < toℕ p) 
                            → (proof-ps : toℕ p < toℕ s) 
                            → (proof-sq : toℕ s < toℕ q) 
                            → Square
                                    (gen r s)
                                    (gen r s)
                                    (fourGenCommutativityConnector r p s q)
                                    (fourGenCommutativityConnector r p s q)


addStrand : {n : ℕ} (b : BPureBraid n) → BPureBraid (suc n)

addStrand base = base
addStrand (gen p q i) = gen (fsuc p) (fsuc q) i
addStrand (identity p i j) = identity (fsuc p) i j
addStrand (genEquality p q i j) = genEquality (fsuc p) (fsuc q) i j
addStrand (twoGenCommutativity1 p q r s proof-rp proof-sp proof-rq proof-sq i j) = twoGenCommutativity1 (fsuc p) (fsuc q) (fsuc r) (fsuc s) (sucP proof-rp) (sucP proof-sp) (sucP proof-rq) (sucP proof-sq) i j
addStrand (twoGenCommutativity2 p q r s proof-pr proof-ps proof-rq proof-sq i j) = twoGenCommutativity2 (fsuc p) (fsuc q) (fsuc r) (fsuc s) (sucP proof-pr) (sucP proof-ps) (sucP proof-rq) (sucP proof-sq) i j

addStrand (threeGenCommutativityConnector r p q i) = threeGenCommutativityConnector (fsuc r) (fsuc p) (fsuc q) i
addStrand (threeGenCommutativityComposition r p q proof-rp proof-pq i j) = threeGenCommutativityComposition (fsuc r) (fsuc p) (fsuc q) (sucP proof-rp)  (sucP proof-pq) i j
addStrand (threeGenCommutativity r p q proof-rp proof-pq i j) = threeGenCommutativity (fsuc r) (fsuc p) (fsuc q) (sucP proof-rp)  (sucP proof-pq) i j
addStrand (fourGenCommutativityConnector r p s q i) = fourGenCommutativityConnector (fsuc r ) (fsuc p) (fsuc s) (fsuc q) i
addStrand (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) = 
    fourGenCommutativityComposition (fsuc r ) (fsuc p) (fsuc s) (fsuc q) (sucP proof-rp) (sucP proof-ps) (sucP proof-sq) i j
addStrand (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) = fourGenCommutativity (fsuc r ) (fsuc p) (fsuc s) (fsuc q) (sucP proof-rp) (sucP proof-ps) (sucP proof-sq) i j


delStrand : {n : ℕ} (b : BPureBraid (suc n)) → BPureBraid n

--base always goes to base
delStrand base = base


-- zeroth strand gets deleted, so generators on that strand cease to exist
delStrand (gen (zero , proof-p) q i ) = base
delStrand (gen (suc p , proof-p) (zero , proof-q) i) = base
delStrand (gen (suc p , proof-p) (suc q , proof-q) i) = gen (p , pred proof-p) (q , pred proof-q) i


-- identity element for zeroth strand is removed
delStrand (identity (zero , proof-p) i j) = base
delStrand (identity (suc p , proof-p) i j) = identity (p , pred proof-p) i j


-- any cases with a zero strand reduce to refl
delStrand (genEquality (zero , proof-p) (zero , proof-q) i j) = base
delStrand (genEquality (zero , proof-p) (suc q , proof-q) i j) = base
delStrand (genEquality (suc p , proof-p) (zero , proof-q) i j) = base
delStrand (genEquality (suc p , proof-p) (suc q , proof-q) i j) = genEquality (p , pred proof-p) (q , pred proof-q) i j


-- if r is zero, gen r s cannot exist so not splitting case on s
delStrand (twoGenCommutativity1 (zero , proof-p) (zero , proof-q) (zero , proof-r) (s , proof-s) proof-rp proof-sp proof-rq proof-sq i j) = base
delStrand (twoGenCommutativity1 (zero , proof-p) (suc q , proof-q) (zero , proof-r) (s , proof-s) proof-rp proof-sp proof-rq proof-sq i j) = base
delStrand (twoGenCommutativity1 (suc p , proof-p) (zero , proof-q) (zero , proof-r) (s , proof-s) proof-rp proof-sp proof-rq proof-sq i j) = base
delStrand (twoGenCommutativity1 (suc p , proof-p) (suc q , proof-q) (zero , proof-r) (s , proof-s) proof-rp proof-sp proof-rq proof-sq i j) = gen (p , pred proof-p) (q , pred proof-q) j

-- if s is zero, gen r s cannot exist so these will reduce to base or gen p q
delStrand (twoGenCommutativity1 (zero , proof-p) (zero , proof-q) (suc r , proof-r) (zero , proof-s) proof-rp proof-sp proof-rq proof-sq i j) = base
delStrand (twoGenCommutativity1 (zero , proof-p) (suc q , proof-q) (suc r , proof-r) (zero , proof-s) proof-rp proof-sp proof-rq proof-sq i j) = base
delStrand (twoGenCommutativity1 (suc p , proof-p) (zero , proof-q) (suc r , proof-r) (zero , proof-s) proof-rp proof-sp proof-rq proof-sq i j) = base
delStrand (twoGenCommutativity1 (suc p , proof-p) (suc q , proof-q) (suc r , proof-r) (zero , proof-s) proof-rp proof-sp proof-rq proof-sq i j) = gen (p , pred proof-p) (q , pred proof-q) j

-- if gen r s exists :
-- if p or q are zero only gen r s remains
delStrand (twoGenCommutativity1 (zero , proof-p) (zero , proof-q) (suc r , proof-r) (suc s , proof-s) proof-rp proof-sp proof-rq proof-sq i j) = gen (r , pred proof-r) (s , pred proof-s) i
delStrand (twoGenCommutativity1 (zero , proof-p) (suc q , proof-q) (suc r , proof-r) (suc s , proof-s) proof-rp proof-sp proof-rq proof-sq i j) = gen (r , pred proof-r) (s , pred proof-s) i
delStrand (twoGenCommutativity1 (suc p , proof-p) (zero , proof-q) (suc r , proof-r) (suc s , proof-s) proof-rp proof-sp proof-rq proof-sq i j) = gen (r , pred proof-r) (s , pred proof-s) i

-- if all strands exist after deletion, map commutativity rule
delStrand (twoGenCommutativity1 (suc p , proof-p) (suc q , proof-q) (suc r , proof-r) (suc s , proof-s) proof-rp proof-sp proof-rq proof-sq i j) =
    twoGenCommutativity1 (p , pred proof-p) (q , pred proof-q) (r , pred proof-r) (s , pred proof-s) (pred proof-rp) (pred proof-sp) (pred proof-rq) (pred proof-sq) i j



-- if p is removed, gen p q cannot exist. no need to case split on q
delStrand (twoGenCommutativity2 (zero , proof-p) q (zero , proof-r) (zero , proof-s) proof-pr proof-ps proof-rq proof-sq i j) = base
delStrand (twoGenCommutativity2 (zero , proof-p) q (zero , proof-r) (suc s , proof-s) proof-pr proof-ps proof-rq proof-sq i j) = base
delStrand (twoGenCommutativity2 (zero , proof-p) q (suc r , proof-r) (zero , proof-s) proof-pr proof-ps proof-rq proof-sq i j) = base
delStrand (twoGenCommutativity2 (zero , proof-p) q (suc r , proof-r) (suc s , proof-s) proof-pr proof-ps proof-rq proof-sq i j) = gen (r , pred proof-r) (s , pred proof-s) i



--if q is zero, either gen r s exists or it does not
delStrand (twoGenCommutativity2 (suc p , proof-p) (zero , proof-q) (zero , proof-r) (zero , proof-s) proof-pr proof-ps proof-rq proof-sq i j) = base
delStrand (twoGenCommutativity2 (suc p , proof-p) (zero , proof-q) (zero , proof-r) (suc s , proof-s) proof-pr proof-ps proof-rq proof-sq i j) = base
delStrand (twoGenCommutativity2 (suc p , proof-p) (zero , proof-q) (suc r , proof-r) (zero , proof-s) proof-pr proof-ps proof-rq proof-sq i j) = base
delStrand (twoGenCommutativity2 (suc p , proof-p) (zero , proof-q) (suc r , proof-r) (suc s , proof-s) proof-pr proof-ps proof-rq proof-sq i j) = gen (r , pred proof-r) (s , pred proof-s) i

-- gen p q exist, if gen r s also exists then we map the rule
delStrand (twoGenCommutativity2 (suc p , proof-p) (suc q , proof-q) (zero , proof-r) (zero , proof-s) proof-pr proof-ps proof-rq proof-sq i j) = gen (p , pred proof-p) (q , pred proof-q) j
delStrand (twoGenCommutativity2 (suc p , proof-p) (suc q , proof-q) (zero , proof-r) (suc s , proof-s) proof-pr proof-ps proof-rq proof-sq i j) = gen (p , pred proof-p) (q , pred proof-q) j
delStrand (twoGenCommutativity2 (suc p , proof-p) (suc q , proof-q) (suc r , proof-r) (zero , proof-s) proof-pr proof-ps proof-rq proof-sq i j) = gen (p , pred proof-p) (q , pred proof-q) j
delStrand (twoGenCommutativity2 (suc p , proof-p) (suc q , proof-q) (suc r , proof-r) (suc s , proof-s) proof-pr proof-ps proof-rq proof-sq i j) =
    twoGenCommutativity2 (p , pred proof-p) (q , pred proof-q) (r , pred proof-r) (s , pred proof-s)  (pred proof-pr) (pred proof-ps) (pred proof-rq) (pred proof-sq) i j




delStrand (threeGenCommutativityConnector (zero , proof-r) (suc p , proof-p) (suc q , proof-q) i) = gen (p , pred proof-p) (q , pred proof-q) i
delStrand (threeGenCommutativityConnector (suc r , proof-r) (zero , proof-p) (suc q , proof-q) i) = gen (r , pred proof-r) (q , pred proof-q) i
delStrand (threeGenCommutativityConnector (suc r , proof-r) (suc p , proof-p) (zero , proof-q) i) = gen (r , pred proof-r) (p , pred proof-p) i
delStrand (threeGenCommutativityConnector (suc r , proof-r) (suc p , proof-p) (suc q , proof-q) i) = threeGenCommutativityConnector (r , pred proof-r) (p , pred proof-p) (q , pred proof-q) i

delStrand (threeGenCommutativityConnector (zero , proof-r) (zero , proof-p) (zero , proof-q) i)  = base
delStrand (threeGenCommutativityConnector (zero , proof-r) (zero , proof-p) (suc q , proof-q) i) = base
delStrand (threeGenCommutativityConnector (zero , proof-r) (suc p , proof-p) (zero , proof-q) i) = base
delStrand (threeGenCommutativityConnector (suc r , proof-r) (zero , proof-p) (zero , proof-q) i) = base

delStrand (threeGenCommutativityComposition (zero , proof-r) (suc p , proof-p) (suc q , proof-q) proof-rp proof-pq i j) = gen (p , pred proof-p) (q , pred proof-q) (i ∨ j)
delStrand (threeGenCommutativityComposition (suc r , proof-r) (zero , proof-p) (suc q , proof-q) proof-rp proof-pq i j) = gen (r , pred proof-r) (q , pred proof-q) (i ∧ ~ j)
delStrand (threeGenCommutativityComposition (suc r , proof-r) (suc p , proof-p) (zero , proof-q) proof-rp  proof-pq i j) = gen (r , pred proof-r) ( p , pred proof-p) i
delStrand (threeGenCommutativityComposition (suc r , proof-r) (suc p , proof-p) (suc q , proof-q) proof-rp  proof-pq i j) = threeGenCommutativityComposition (r , pred proof-r) (p , pred proof-p) (q , pred proof-q) (pred proof-rp)  (pred proof-pq) i j

delStrand (threeGenCommutativityComposition (zero , proof-r) (zero , proof-p) (zero , proof-q) proof-rp  proof-pq i j)  = base
delStrand (threeGenCommutativityComposition (zero , proof-r) (zero , proof-p) (suc q , proof-q) proof-rp  proof-pq i j) = base
delStrand (threeGenCommutativityComposition (zero , proof-r) (suc p , proof-p) (zero , proof-q) proof-rp  proof-pq i j) = base
delStrand (threeGenCommutativityComposition (suc r , proof-r) (zero , proof-p) (zero , proof-q) proof-rp  proof-pq i j) = base

delStrand (threeGenCommutativity (zero , proof-r) (suc p , proof-p) (suc q , proof-q) proof-rp  proof-pq i j) = genEquality (p , pred proof-p) (q , pred proof-q) i j 
delStrand (threeGenCommutativity (suc r , proof-r) (zero , proof-p) (suc q , proof-q) proof-rp  proof-pq i j) = genEquality (r , pred proof-r) (q , pred proof-q) i j
delStrand (threeGenCommutativity (suc r , proof-r) (suc p , proof-p) (zero , proof-q) proof-rp  proof-pq i j) = gen (r , pred proof-r) (p , pred proof-p) j 
delStrand (threeGenCommutativity (suc r , proof-r) (suc p , proof-p) (suc q , proof-q) proof-rp  proof-pq i j) = threeGenCommutativity (r , pred proof-r) (p , pred proof-p) (q , pred proof-q) (pred proof-rp)  (pred proof-pq) i j

delStrand (threeGenCommutativity (zero , proof-r) (zero , proof-p) (zero , proof-q) proof-rp  proof-pq i j) = base
delStrand (threeGenCommutativity (zero , proof-r) (zero , proof-p) (suc q , proof-q) proof-rp  proof-pq i j) = base
delStrand (threeGenCommutativity (zero , proof-r) (suc p , proof-p) (zero , proof-q) proof-rp  proof-pq i j) = base
delStrand (threeGenCommutativity (suc r , proof-r) (zero , proof-p) (zero , proof-q) proof-rp  proof-pq i j) = base




delStrand (fourGenCommutativityConnector (zero , proof-r) (zero , proof-p) (zero , proof-s) (zero , proof-q) i) = base
delStrand (fourGenCommutativityConnector (zero , proof-r) (zero , proof-p) (zero , proof-s) (suc q , proof-q) i) =   base
delStrand (fourGenCommutativityConnector (zero , proof-r) (zero , proof-p) (suc s , proof-s) (zero , proof-q) i) = base
delStrand (fourGenCommutativityConnector (zero , proof-r) (zero , proof-p) (suc s , proof-s) (suc q , proof-q) i) =  gen (s , pred proof-s) (q , pred proof-q) i
delStrand (fourGenCommutativityConnector (zero , proof-r) (suc p , proof-p) (zero , proof-s) (zero , proof-q) i) =  base
delStrand (fourGenCommutativityConnector (zero , proof-r) (suc p , proof-p) (zero , proof-s) (suc q , proof-q) i) =  gen (p , pred proof-p) (q , pred proof-q) i  
delStrand (fourGenCommutativityConnector (zero , proof-r) (suc p , proof-p) (suc s , proof-s) (zero , proof-q) i) =   base
delStrand (fourGenCommutativityConnector (suc r , proof-r) (zero , proof-p) (zero , proof-s) (zero , proof-q) i) =  base
delStrand (fourGenCommutativityConnector (suc r , proof-r) (zero , proof-p) (zero , proof-s) (suc q , proof-q) i) =  gen (r , pred proof-r) (q , pred proof-q) i  
delStrand (fourGenCommutativityConnector (suc r , proof-r) (zero , proof-p) (suc s , proof-s) (zero , proof-q) i) =   base
delStrand (fourGenCommutativityConnector (suc r , proof-r) (zero , proof-p) (suc s , proof-s) (suc q , proof-q) i) =  base
delStrand (fourGenCommutativityConnector (suc r , proof-r) (suc p , proof-p) (zero , proof-s) (zero , proof-q) i) =   base
delStrand (fourGenCommutativityConnector (suc r , proof-r) (suc p , proof-p) (zero , proof-s) (suc q , proof-q) i) =  base
delStrand (fourGenCommutativityConnector (suc r , proof-r) (suc p , proof-p) (suc s , proof-s) (zero , proof-q) i) =  base


--valid cases
delStrand (fourGenCommutativityConnector (zero , proof-r) (suc p , proof-p) (suc s , proof-s) (suc q , proof-q) i) =
    ((gen (p , pred proof-p) (q , pred proof-q)) ∙ (gen (s , pred proof-s) (q , pred proof-q))) i


delStrand (fourGenCommutativityConnector (suc r , proof-r) (suc p , proof-p) (suc s , proof-s) (suc q , proof-q) i) = fourGenCommutativityConnector
                                                                                                                                                     (r , pred proof-r) (p , pred proof-p)
                                                                                                                                                     (s , pred proof-s) (q , pred proof-q) i


delStrand (fourGenCommutativityComposition (zero , proof-r) (zero , proof-p) (zero , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq i j) =  base
delStrand (fourGenCommutativityComposition (zero , proof-r) (zero , proof-p) (zero , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq i j) =   base
delStrand (fourGenCommutativityComposition (zero , proof-r) (zero , proof-p) (suc s , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq i j) =   base
delStrand (fourGenCommutativityComposition (zero , proof-r) (zero , proof-p) (suc s , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq i j) = gen (s , pred proof-s) (q , pred proof-q) (i ∧ (~ j))   
delStrand (fourGenCommutativityComposition (zero , proof-r) (suc p , proof-p) (zero , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq i j) =   base 
delStrand (fourGenCommutativityComposition (zero , proof-r) (suc p , proof-p) (zero , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq i j) =   gen (p , pred proof-p) (q , pred proof-q) i  
delStrand (fourGenCommutativityComposition (zero , proof-r) (suc p , proof-p) (suc s , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq i j) =  base  
delStrand (fourGenCommutativityComposition (suc r , proof-r) (zero , proof-p) (zero , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq i j) =   base 
delStrand (fourGenCommutativityComposition (suc r , proof-r) (zero , proof-p) (zero , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq i j) =   gen (r , pred proof-r) (q , pred proof-q) (i ∨ j)
delStrand (fourGenCommutativityComposition (suc r , proof-r) (zero , proof-p) (suc s , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq i j) =   base 
delStrand (fourGenCommutativityComposition (suc r , proof-r) (zero , proof-p) (suc s , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq i j) = ⊥.rec 
                                                                                                                                                    {A = Square 
                                                                                                                                                    (gen (r , pred proof-r) (q , pred proof-q)) 
                                                                                                                                                    (sym (gen (s , pred proof-s) (q , pred proof-q))) 
                                                                                                                                                    refl refl }
                                                                                                                                                    (¬-<-zero proof-rp) i j
                                                                                                                                                    
delStrand (fourGenCommutativityComposition (suc r , proof-r) (suc p , proof-p) (zero , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq i j) =  base  
delStrand (fourGenCommutativityComposition (suc r , proof-r) (suc p , proof-p) (zero , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq i j) = ⊥.rec 
                                                                                                                                                    {A = Square 
                                                                                                                                                    (gen (r , pred proof-r) (q , pred proof-q) ) 
                                                                                                                                                    refl refl 
                                                                                                                                                    (gen (p , pred proof-p) (q , pred proof-q)) }
                                                                                                                                                    (¬-<-zero proof-ps) i j
                                                                                                                                                    
delStrand (fourGenCommutativityComposition (suc r , proof-r) (suc p , proof-p) (suc s , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq i j) =   base 

--valid cases

delStrand (fourGenCommutativityComposition (zero , proof-r) (suc p , proof-p) (suc s , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq i j) = compPath-filler 
                                                                                                                                                    (gen (p , pred proof-p) 
                                                                                                                                                    ( q , pred proof-q  )) 
                                                                                                                                                    (gen (s , pred proof-s) (q , pred proof-q) ) 
                                                                                                                                                    (~ j) i

delStrand (fourGenCommutativityComposition (suc r , proof-r) (suc p , proof-p) (suc s , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq i j) = fourGenCommutativityComposition
                                                                                                                                                     (r , pred proof-r) (p , pred proof-p)
                                                                                                                                                     (s , pred proof-s) (q , pred proof-q)
                                                                                                                                                     (pred proof-rp) (pred proof-ps) (pred proof-sq) i j



delStrand (fourGenCommutativity (zero , proof-r) (zero , proof-p) (zero , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq i j) = base
delStrand (fourGenCommutativity (zero , proof-r) (zero , proof-p) (zero , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq i j) =   base
delStrand (fourGenCommutativity (zero , proof-r) (zero , proof-p) (suc s , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq i j) = base
delStrand (fourGenCommutativity (zero , proof-r) (zero , proof-p) (suc s , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq i j) =  gen (s , pred proof-s) (q , pred proof-q) i
delStrand (fourGenCommutativity (zero , proof-r) (suc p , proof-p) (zero , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq i j) =  base
delStrand (fourGenCommutativity (zero , proof-r) (suc p , proof-p) (zero , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq i j) =  gen (p , pred proof-p) (q , pred proof-q) i  
delStrand (fourGenCommutativity (zero , proof-r) (suc p , proof-p) (suc s , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq i j) =   base
delStrand (fourGenCommutativity (suc r , proof-r) (zero , proof-p) (zero , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq i j) =  base
delStrand (fourGenCommutativity (suc r , proof-r) (zero , proof-p) (zero , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq i j) =  gen (r , pred proof-r) (q , pred proof-q) i  
delStrand (fourGenCommutativity (suc r , proof-r) (zero , proof-p) (suc s , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq i j) =   gen (r , pred proof-r) (s , pred proof-s) j 
delStrand (fourGenCommutativity (suc r , proof-r) (zero , proof-p) (suc s , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq i j) =  gen (r , pred proof-r) (s , pred proof-s) j 
delStrand (fourGenCommutativity (suc r , proof-r) (suc p , proof-p) (zero , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq i j) =   base
delStrand (fourGenCommutativity (suc r , proof-r) (suc p , proof-p) (zero , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq i j) =  base
delStrand (fourGenCommutativity (suc r , proof-r) (suc p , proof-p) (suc s , proof-s) (zero , proof-q) proof-rp proof-ps proof-sq i j) =  gen (r , pred proof-r) (s , pred proof-s) j 

--valid cases
delStrand (fourGenCommutativity (zero , proof-r) (suc p , proof-p) (suc s , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq i j) = 
    ((gen (p , pred proof-p) (q , pred proof-q)) ∙ (gen (s , pred proof-s) (q , pred proof-q))) i
delStrand (fourGenCommutativity (suc r , proof-r) (suc p , proof-p) (suc s , proof-s) (suc q , proof-q) proof-rp proof-ps proof-sq i j) = fourGenCommutativity
                                                                                                                                          (r , pred proof-r) (p , pred proof-p)
                                                                                                                                          (s , pred proof-s) (q , pred proof-q)
                                                                                                                                          (pred proof-rp) (pred proof-ps) (pred proof-sq) i j
 