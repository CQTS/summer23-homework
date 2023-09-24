{-# OPTIONS --safe #-}
module Braid.OLD.Isomorphism.to where

open import Cubical.Foundations.Prelude

open import Braid.OLD.PureBraidAlt
open import Braid.OLD.PureBraidDefinitions.PureBraid
open import Cubical.Data.Nat.Order renaming (pred-≤-pred to pred ; <-weaken to weaken; <-asym to asym ; <-trans to trans ; <→≢ to <!=)
open import Cubical.Data.Nat
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Fin






BPureBraid→BPureBraid' : ∀ n → (b : BPureBraid n) → BPureBraid' n
BPureBraid→BPureBraid' n base = base
BPureBraid→BPureBraid' n (gen p q i) with fst p ≟ fst q
... | (lt proof) = gen p q proof i
... | (eq proof) = base
... | (gt proof) =  gen q p proof i


-- identity if generator is on one strand : ∀ p : (gen p p ) ≡ refl 
BPureBraid→BPureBraid' n (identity p i j) with fst p ≟ fst p 
... | (lt proof) =  ⊥.rec {A = Square (gen p p proof) refl refl refl} (¬m<m proof) i j
... | (eq proof) = base
... | (gt proof) =  ⊥.rec {A = Square (gen p p proof) refl refl refl} (¬m<m proof) i j


-- generators on same strands are equal : (gen p q ) ≡ (gen q p) 
BPureBraid→BPureBraid' n (genEquality p q i j) with fst p ≟ fst q
BPureBraid→BPureBraid' n (genEquality p q i j) | (lt proof) with fst q ≟ fst p
BPureBraid→BPureBraid' n (genEquality p q i j) | (lt proof) | (lt proof2) = ⊥.rec {A = Square (gen p q proof) (gen q p proof2) refl refl} (asym proof (weaken proof2)) i j
BPureBraid→BPureBraid' n (genEquality p q i j) | (lt proof) | (eq proof2) = ⊥.rec {A = Square (gen p q proof) refl refl refl} (<!= proof (sym proof2)) i j
BPureBraid→BPureBraid' n (genEquality p q i j) | (lt proof) | (gt proof2) = gen p q (isProp≤ proof proof2 i) j  -- (isProp≤ proof proof2 i)

BPureBraid→BPureBraid' n (genEquality p q i j) | (eq proof) with fst q ≟ fst p
BPureBraid→BPureBraid' n (genEquality p q i j) | (eq proof) | (lt proof2) = ⊥.rec {A = Square refl (gen q p proof2) refl refl} (<!= proof2 (sym proof)) i j
BPureBraid→BPureBraid' n (genEquality p q i j) | (eq proof) | (eq proof2) = base
BPureBraid→BPureBraid' n (genEquality p q i j) | (eq proof) | (gt proof2) = ⊥.rec {A = Square refl (gen p q proof2) refl refl} (<!= proof2 proof) i j

BPureBraid→BPureBraid' n (genEquality p q i j) | (gt proof) with fst q ≟ fst p 
BPureBraid→BPureBraid' n (genEquality p q i j) | (gt proof) | (lt proof2) = gen q p (isProp≤ proof proof2 i) j
BPureBraid→BPureBraid' n (genEquality p q i j) | (gt proof) | (eq proof2) = ⊥.rec {A = Square (gen q p proof) refl refl refl} (<!= proof proof2) i j
BPureBraid→BPureBraid' n (genEquality p q i j) | (gt proof) | (gt proof2) = ⊥.rec {A = Square (gen q p proof) (gen p q proof2) refl refl} (asym proof (weaken proof2)) i j


-- commutativity with two generators : (gen p q ) ∙ (gen r s ) ≡ (gen r s ) (gen p q ) iff r < s < p < q

BPureBraid→BPureBraid' n (twoGenCommutativity1 p q r s proof-rp proof-sp proof-rq proof-sq i j) with fst p ≟ fst q

BPureBraid→BPureBraid' n (twoGenCommutativity1 p q r s proof-rp proof-sp proof-rq proof-sq i j) | (lt proof) with fst r ≟ fst s
BPureBraid→BPureBraid' n (twoGenCommutativity1 p q r s proof-rp proof-sp proof-rq proof-sq i j) | (lt proof) | (lt proof2) = twoGenCommutativity1 p q r s proof2 proof-sp proof i j
BPureBraid→BPureBraid' n (twoGenCommutativity1 p q r s proof-rp proof-sp proof-rq proof-sq i j) | (lt proof) | (eq proof2) = gen p q proof j
BPureBraid→BPureBraid' n (twoGenCommutativity1 p q r s proof-rp proof-sp proof-rq proof-sq i j) | (lt proof) | (gt proof2) = twoGenCommutativity1 p q s r proof2 proof-rp proof i j

BPureBraid→BPureBraid' n (twoGenCommutativity1 p q r s proof-rp proof-sp proof-rq proof-sq i j) | (eq proof) with fst r ≟ fst s
BPureBraid→BPureBraid' n (twoGenCommutativity1 p q r s proof-rp proof-sp proof-rq proof-sq i j) | (eq proof) | (lt proof2) = gen r s proof2 i 
BPureBraid→BPureBraid' n (twoGenCommutativity1 p q r s proof-rp proof-sp proof-rq proof-sq i j) | (eq proof) | (eq proof2) = base
BPureBraid→BPureBraid' n (twoGenCommutativity1 p q r s proof-rp proof-sp proof-rq proof-sq i j) | (eq proof) | (gt proof2) = gen s r proof2 i


BPureBraid→BPureBraid' n (twoGenCommutativity1 p q r s proof-rp proof-sp proof-rq proof-sq i j) | (gt proof) with fst r ≟ fst s
BPureBraid→BPureBraid' n (twoGenCommutativity1 p q r s proof-rp proof-sp proof-rq proof-sq i j) | (gt proof) | (lt proof2) = twoGenCommutativity1 q p r s proof2 proof-sq proof i j 
BPureBraid→BPureBraid' n (twoGenCommutativity1 p q r s proof-rp proof-sp proof-rq proof-sq i j) | (gt proof) | (eq proof2) = gen q p proof j
BPureBraid→BPureBraid' n (twoGenCommutativity1 p q r s proof-rp proof-sp proof-rq proof-sq i j) | (gt proof) | (gt proof2) = twoGenCommutativity1 q p s r proof2 proof-rq proof i j 


-- commutativity with two generators : (gen p q ) ∙ (gen r s ) ≡ (gen r s ) (gen p q ) iff p < r < s < q

BPureBraid→BPureBraid' n (twoGenCommutativity2 p q r s proof-pr proof-ps proof-rq proof-sq i j) with fst p ≟ fst q
BPureBraid→BPureBraid' n (twoGenCommutativity2 p q r s proof-pr proof-ps proof-rq proof-sq i j) | (lt proof) with fst r ≟ fst s
BPureBraid→BPureBraid' n (twoGenCommutativity2 p q r s proof-pr proof-ps proof-rq proof-sq i j) | (lt proof) | (lt proof2) = twoGenCommutativity2 p q r s proof-pr proof2 proof-sq proof i j 
BPureBraid→BPureBraid' n (twoGenCommutativity2 p q r s proof-pr proof-ps proof-rq proof-sq i j) | (lt proof) | (eq proof2) = gen p q proof j 
BPureBraid→BPureBraid' n (twoGenCommutativity2 p q r s proof-pr proof-ps proof-rq proof-sq i j) | (lt proof) | (gt proof2) = twoGenCommutativity2 p q s r proof-ps proof2 proof-rq proof i j 

BPureBraid→BPureBraid' n (twoGenCommutativity2 p q r s proof-pr proof-ps proof-rq proof-sq i j) | (eq proof) with fst r ≟ fst s
BPureBraid→BPureBraid' n (twoGenCommutativity2 p q r s proof-pr proof-ps proof-rq proof-sq i j) | (eq proof) | (lt proof2) = gen r s proof2 i 
BPureBraid→BPureBraid' n (twoGenCommutativity2 p q r s proof-pr proof-ps proof-rq proof-sq i j) | (eq proof) | (eq proof2) = base 
BPureBraid→BPureBraid' n (twoGenCommutativity2 p q r s proof-pr proof-rs proof-rq proof-sq i j) | (eq proof) | (gt proof2) = gen s r proof2 i 
    

BPureBraid→BPureBraid' n (twoGenCommutativity2 p q r s proof-pr proof-ps proof-rq proof-sq i j) | (gt proof) with fst r ≟ fst s
BPureBraid→BPureBraid' n (twoGenCommutativity2 p q r s proof-pr proof-ps proof-rq proof-sq i j) | (gt proof) | (lt proof2) = twoGenCommutativity2 q p r s (trans proof proof-pr) proof2 (trans proof-sq proof) proof i j 
BPureBraid→BPureBraid' n (twoGenCommutativity2 p q r s proof-pr proof-ps proof-rq proof-sq i j) | (gt proof) | (eq proof2) = gen q p proof j 
BPureBraid→BPureBraid' n (twoGenCommutativity2 p q r s proof-pr proof-ps proof-rq proof-sq i j) | (gt proof) | (gt proof2) = twoGenCommutativity2 q p s r (trans proof proof-ps) proof2 (trans proof-rq proof) proof i j




BPureBraid→BPureBraid' n (threeGenCommutativityConnector r p q i) = {!   !}
--  with fst p ≟ fst q
-- BPureBraid→BPureBraid' n (threeGenCommutativityConnector r p q proof-rp proof-pq i) | (lt proof) with fst r ≟ fst p
-- BPureBraid→BPureBraid' n (threeGenCommutativityConnector r p q proof-rp proof-pq i) | (lt proof) | (lt proof2) with fst r ≟ fst q
-- BPureBraid→BPureBraid' n (threeGenCommutativityConnector r p q proof-rp proof-pq i) | (lt proof) | (lt proof2) | (lt proof3) = threeGenCommutativityConnector r p q proof2 proof proof3 i -- only possible case
-- BPureBraid→BPureBraid' n (threeGenCommutativityConnector r p q proof-rp proof-pq i) | (lt proof) | (lt proof2) | (eq proof3) = base 
-- BPureBraid→BPureBraid' n (threeGenCommutativityConnector r p q proof-rp proof-pq i) | (lt proof) | (lt proof2) | (gt proof3) = base

-- BPureBraid→BPureBraid' n (threeGenCommutativityConnector r p q proof-rp proof-pq i) | (lt proof) | (eq proof2) with fst r ≟ fst q
-- BPureBraid→BPureBraid' n (threeGenCommutativityConnector r p q proof-rp proof-pq i) | (lt proof) | (eq proof2) | (lt proof3) = base 
-- BPureBraid→BPureBraid' n (threeGenCommutativityConnector r p q proof-rp proof-pq i) | (lt proof) | (eq proof2) | (eq proof3) = base
-- BPureBraid→BPureBraid' n (threeGenCommutativityConnector r p q proof-rp proof-pq i) | (lt proof) | (eq proof2) | (gt proof3) = base

-- BPureBraid→BPureBraid' n (threeGenCommutativityConnector r p q proof-rp proof-pq i) | (lt proof) | (gt proof2) with fst r ≟ fst q    
-- BPureBraid→BPureBraid' n (threeGenCommutativityConnector r p q proof-rp proof-pq i) | (lt proof) | (gt proof2) | (lt proof3) = base 
-- BPureBraid→BPureBraid' n (threeGenCommutativityConnector r p q proof-rp proof-pq i) | (lt proof) | (gt proof2) | (eq proof3) = base
-- BPureBraid→BPureBraid' n (threeGenCommutativityConnector r p q proof-rp proof-pq i) | (lt proof) | (gt proof2) | (gt proof3) = base



-- BPureBraid→BPureBraid' n (threeGenCommutativityConnector r p q proof-rp proof-pq i) | (eq proof) with fst r ≟ fst p
-- BPureBraid→BPureBraid' n (threeGenCommutativityConnector r p q proof-rp proof-pq i) | (eq proof) | (lt proof2) with fst r ≟ fst q
-- BPureBraid→BPureBraid' n (threeGenCommutativityConnector r p q proof-rp proof-pq i) | (eq proof) | (lt proof2) | (lt proof3) = base      
-- BPureBraid→BPureBraid' n (threeGenCommutativityConnector r p q proof-rp proof-pq i) | (eq proof) | (lt proof2) | (eq proof3) = base 
-- BPureBraid→BPureBraid' n (threeGenCommutativityConnector r p q proof-rp proof-pq i) | (eq proof) | (lt proof2) | (gt proof3) = base

-- BPureBraid→BPureBraid' n (threeGenCommutativityConnector r p q proof-rp proof-pq i) | (eq proof) | (eq proof2) with fst r ≟ fst q
-- BPureBraid→BPureBraid' n (threeGenCommutativityConnector r p q proof-rp proof-pq i) | (eq proof) | (eq proof2) | (lt proof3) = base
-- BPureBraid→BPureBraid' n (threeGenCommutativityConnector r p q proof-rp proof-pq i) | (eq proof) | (eq proof2) | (eq proof3) = base          
-- BPureBraid→BPureBraid' n (threeGenCommutativityConnector r p q proof-rp proof-pq i) | (eq proof) | (eq proof2) | (gt proof3) = base

-- BPureBraid→BPureBraid' n (threeGenCommutativityConnector r p q proof-rp proof-pq i) | (eq proof) | (gt proof2) with fst r ≟ fst q
-- BPureBraid→BPureBraid' n (threeGenCommutativityConnector r p q proof-rp proof-pq i) | (eq proof) | (gt proof2) | (lt proof3) = base
-- BPureBraid→BPureBraid' n (threeGenCommutativityConnector r p q proof-rp proof-pq i) | (eq proof) | (gt proof2) | (eq proof3) = base
-- BPureBraid→BPureBraid' n (threeGenCommutativityConnector r p q proof-rp proof-pq i) | (eq proof) | (gt proof2) | (gt proof3) = base       



-- BPureBraid→BPureBraid' n (threeGenCommutativityConnector r p q proof-rp proof-pq i) | (gt proof) with fst r ≟ fst p
-- BPureBraid→BPureBraid' n (threeGenCommutativityConnector r p q proof-rp proof-pq i) | (gt proof) | (lt proof2) with fst r ≟ fst q
-- BPureBraid→BPureBraid' n (threeGenCommutativityConnector r p q proof-rp proof-pq i) | (gt proof) | (lt proof2) | (lt proof3) = base   
-- BPureBraid→BPureBraid' n (threeGenCommutativityConnector r p q proof-rp proof-pq i) | (gt proof) | (lt proof2) | (eq proof3) = base
-- BPureBraid→BPureBraid' n (threeGenCommutativityConnector r p q proof-rp proof-pq i) | (gt proof) | (lt proof2) | (gt proof3) = base

-- BPureBraid→BPureBraid' n (threeGenCommutativityConnector r p q proof-rp proof-pq i) | (gt proof) | (eq proof2) with fst r ≟ fst q
-- BPureBraid→BPureBraid' n (threeGenCommutativityConnector r p q proof-rp proof-pq i) | (gt proof) | (eq proof2) | (lt proof3) = base   
-- BPureBraid→BPureBraid' n (threeGenCommutativityConnector r p q proof-rp proof-pq i) | (gt proof) | (eq proof2) | (eq proof3) = base
-- BPureBraid→BPureBraid' n (threeGenCommutativityConnector r p q proof-rp proof-pq i) | (gt proof) | (eq proof2) | (gt proof3) = base

-- BPureBraid→BPureBraid' n (threeGenCommutativityConnector r p q proof-rp proof-pq i) | (gt proof) | (gt proof2) with fst r ≟ fst q
-- BPureBraid→BPureBraid' n (threeGenCommutativityConnector r p q proof-rp proof-pq i) | (gt proof) | (gt proof2) | (lt proof3) = base   
-- BPureBraid→BPureBraid' n (threeGenCommutativityConnector r p q proof-rp proof-pq i) | (gt proof) | (gt proof2) | (eq proof3) = base
-- BPureBraid→BPureBraid' n (threeGenCommutativityConnector r p q proof-rp proof-pq i) | (gt proof) | (gt proof2) | (gt proof3) = base -- only possible case




-------------------------------------------------------------------------------------------------------------------------------------------

-- BPureBraid→BPureBraid' n (threeGenCommutativityLeft r p q proof-rp proof-pq i j) with fst p ≟ fst q


-- BPureBraid→BPureBraid' n (threeGenCommutativityLeft r p q proof-rp proof-pq i j) | (lt proof) with fst r ≟ fst p
-- BPureBraid→BPureBraid' n (threeGenCommutativityLeft r p q proof-rp proof-pq i j) | (lt proof) | (lt proof2) with fst r ≟ fst q
-- BPureBraid→BPureBraid' n (threeGenCommutativityLeft r p q proof-rp proof-pq i j) | (lt proof) | (lt proof2) | (lt proof3) =  threeGenCommutativityLeft r p q proof2 proof proof3 i j -- 1st possible case
-- BPureBraid→BPureBraid' n (threeGenCommutativityLeft r p q proof-rp proof-pq i j) | (lt proof) | (lt proof2) | (eq proof3) =  ⊥.rec {A = Square (gen p q proof) refl refl (gen r p proof2)} (<!= (trans proof-rp proof-pq) proof3) i j
-- BPureBraid→BPureBraid' n (threeGenCommutativityLeft r p q proof-rp proof-pq i j) | (lt proof) | (lt proof2) | (gt proof3) =  ⊥.rec {A = Square (gen p q proof) (sym(gen q r proof3)) refl (gen r p proof2)} (asym (trans proof-rp proof-pq) (weaken proof3)) i j 


-- BPureBraid→BPureBraid' n (threeGenCommutativityLeft r p q proof-rp proof-pq i j) | (lt proof) | (eq proof2) with fst r ≟ fst q
-- BPureBraid→BPureBraid' n (threeGenCommutativityLeft r p q proof-rp proof-pq i j) | (lt proof) | (eq proof2) | (lt proof3) =  ⊥.rec {A = Square (gen p q proof) (sym (gen r q proof3)) refl refl} (<!= proof-rp proof2) i j 
-- BPureBraid→BPureBraid' n (threeGenCommutativityLeft r p q proof-rp proof-pq i j) | (lt proof) | (eq proof2) | (eq proof3) =  ⊥.rec {A = Square (gen p q proof) refl refl refl } (<!= proof-rp proof2) i j 
-- BPureBraid→BPureBraid' n (threeGenCommutativityLeft r p q proof-rp proof-pq i j) | (lt proof) | (eq proof2) | (gt proof3) =  ⊥.rec {A = Square (gen p q proof) (sym (gen q r proof3)) refl refl } (<!= proof-rp proof2) i j 


-- BPureBraid→BPureBraid' n (threeGenCommutativityLeft r p q proof-rp proof-pq i j) | (lt proof) | (gt proof2) with fst r ≟ fst q 
-- BPureBraid→BPureBraid' n (threeGenCommutativityLeft r p q proof-rp proof-pq i j) | (lt proof) | (gt proof2) | (lt proof3) =  ⊥.rec {A = Square (gen p q proof) (sym (gen r q proof3)) refl (gen p r proof2)} (asym proof2 (weaken proof-rp)) i j 
-- BPureBraid→BPureBraid' n (threeGenCommutativityLeft r p q proof-rp proof-pq i j) | (lt proof) | (gt proof2) | (eq proof3) =  ⊥.rec {A = Square (gen p q proof) refl refl (gen p r proof2)} (asym proof-rp (weaken proof2))  i j 
-- BPureBraid→BPureBraid' n (threeGenCommutativityLeft r p q proof-rp proof-pq i j) | (lt proof) | (gt proof2) | (gt proof3) =  ⊥.rec {A = Square (gen p q proof) (sym (gen q r proof3)) refl (gen p r proof2)} (asym proof-rp (weaken proof2)) i j 



-- BPureBraid→BPureBraid' n (threeGenCommutativityLeft r p q proof-rp proof-pq i j) | (eq proof) with fst r ≟ fst p
-- BPureBraid→BPureBraid' n (threeGenCommutativityLeft r p q proof-rp proof-pq i j) | (eq proof) | (lt proof2) with fst r ≟ fst q
-- BPureBraid→BPureBraid' n (threeGenCommutativityLeft r p q proof-rp proof-pq i j) | (eq proof) | (lt proof2) | (lt proof3) =  ⊥.rec {A = Square refl (sym (gen r q proof3)) refl (gen r p proof2)} (<!= proof-pq proof) i j 
-- BPureBraid→BPureBraid' n (threeGenCommutativityLeft r p q proof-rp proof-pq i j) | (eq proof) | (lt proof2) | (eq proof3) =  ⊥.rec {A = Square refl refl refl (gen r p proof2)} (<!= proof-pq proof) i j 
-- BPureBraid→BPureBraid' n (threeGenCommutativityLeft r p q proof-rp proof-pq i j) | (eq proof) | (lt proof2) | (gt proof3) =  ⊥.rec {A = Square refl (sym (gen q r proof3)) refl (gen r p proof2)} (<!= proof-pq proof) i j 

-- BPureBraid→BPureBraid' n (threeGenCommutativityLeft r p q proof-rp proof-pq i j) | (eq proof) | (eq proof2) with fst r ≟ fst q
-- BPureBraid→BPureBraid' n (threeGenCommutativityLeft r p q proof-rp proof-pq i j) | (eq proof) | (eq proof2) | (lt proof3) =  ⊥.rec {A = Square refl (sym (gen r q proof3)) refl refl} (<!= proof-pq proof) i j 
-- BPureBraid→BPureBraid' n (threeGenCommutativityLeft r p q proof-rp proof-pq i j) | (eq proof) | (eq proof2) | (eq proof3) =  base         
-- BPureBraid→BPureBraid' n (threeGenCommutativityLeft r p q proof-rp proof-pq i j) | (eq proof) | (eq proof2) | (gt proof3) =  ⊥.rec {A = Square refl (sym (gen q r proof3)) refl refl} (<!= proof-pq proof) i j 

-- BPureBraid→BPureBraid' n (threeGenCommutativityLeft r p q proof-rp proof-pq i j) | (eq proof) | (gt proof2) with fst r ≟ fst q
-- BPureBraid→BPureBraid' n (threeGenCommutativityLeft r p q proof-rp proof-pq i j) | (eq proof) | (gt proof2) | (lt proof3) =  ⊥.rec {A = Square refl (sym (gen r q proof3)) refl (gen p r proof2) } (<!= proof-pq proof) i j 
-- BPureBraid→BPureBraid' n (threeGenCommutativityLeft r p q proof-rp proof-pq i j) | (eq proof) | (gt proof2) | (eq proof3) =  ⊥.rec {A = Square refl refl refl (gen p r proof2)} (<!= proof-pq proof) i j 
-- BPureBraid→BPureBraid' n (threeGenCommutativityLeft r p q proof-rp proof-pq i j) | (eq proof) | (gt proof2) | (gt proof3) =  ⊥.rec {A = Square refl (sym (gen q r proof3)) refl (gen p r proof2) } (<!= proof-pq proof) i j 



-- BPureBraid→BPureBraid' n (threeGenCommutativityLeft r p q proof-rp proof-pq i j) | (gt proof) with fst r ≟ fst p 
-- BPureBraid→BPureBraid' n (threeGenCommutativityLeft r p q proof-rp proof-pq i j) | (gt proof) | (lt proof2) with fst r ≟ fst q
-- BPureBraid→BPureBraid' n (threeGenCommutativityLeft r p q proof-rp proof-pq i j) | (gt proof) | (lt proof2) | (lt proof3) =  ⊥.rec {A = Square (gen q p proof) (sym (gen r q proof3)) refl (gen r p proof2)} (asym proof (weaken proof-pq)) i j 
-- BPureBraid→BPureBraid' n (threeGenCommutativityLeft r p q proof-rp proof-pq i j) | (gt proof) | (lt proof2) | (eq proof3) =  ⊥.rec {A = Square (gen q p proof) refl refl (gen r p proof2)} (asym proof (weaken proof-pq)) i j 
-- BPureBraid→BPureBraid' n (threeGenCommutativityLeft r p q proof-rp proof-pq i j) | (gt proof) | (lt proof2) | (gt proof3) =  ⊥.rec {A = Square (gen q p proof) (sym (gen q r proof3)) refl (gen r p proof2)} (asym proof (weaken proof-pq)) i j 

-- BPureBraid→BPureBraid' n (threeGenCommutativityLeft r p q proof-rp proof-pq i j) | (gt proof) | (eq proof2) with fst r ≟ fst q
-- BPureBraid→BPureBraid' n (threeGenCommutativityLeft r p q proof-rp proof-pq i j) | (gt proof) | (eq proof2) | (lt proof3) =  ⊥.rec {A = Square (gen q p proof) (sym (gen r q proof3)) refl refl} (asym proof (weaken proof-pq)) i j 
-- BPureBraid→BPureBraid' n (threeGenCommutativityLeft r p q proof-rp proof-pq i j) | (gt proof) | (eq proof2) | (eq proof3) =  ⊥.rec {A = Square (gen q p proof) refl refl refl} (asym proof (weaken proof-pq)) i j 
-- BPureBraid→BPureBraid' n (threeGenCommutativityLeft r p q proof-rp proof-pq i j) | (gt proof) | (eq proof2) | (gt proof3) =  ⊥.rec {A = Square (gen q p proof) (sym (gen q r proof3)) refl refl} (asym proof (weaken proof-pq)) i j 

-- BPureBraid→BPureBraid' n (threeGenCommutativityLeft r p q proof-rp proof-pq i j) | (gt proof) | (gt proof2) with fst r ≟ fst q
-- BPureBraid→BPureBraid' n (threeGenCommutativityLeft r p q proof-rp proof-pq i j) | (gt proof) | (gt proof2) | (lt proof3) =  ⊥.rec {A = Square (gen q p proof) (sym (gen r q proof3)) refl (gen p r proof2)} (asym proof (weaken proof-pq)) i j 
-- BPureBraid→BPureBraid' n (threeGenCommutativityLeft r p q proof-rp proof-pq i j) | (gt proof) | (gt proof2) | (eq proof3) =  ⊥.rec {A = Square (gen q p proof) refl refl (gen p r proof2)} (asym proof (weaken proof-pq)) i j 
-- BPureBraid→BPureBraid' n (threeGenCommutativityLeft r p q proof-rp proof-pq i j) | (gt proof) | (gt proof2) | (gt proof3) =  ⊥.rec {A = Square (gen q p proof) (sym (gen q r proof3)) refl (gen p r proof2)} (asym proof (weaken proof-pq)) i j -- 2nd possible case maybe??


-- -------------------------------------------------------------------------------------------------------------------------------------------

-- BPureBraid→BPureBraid' n (threeGenCommutativityMiddle r p q proof-rp proof-pq i j) with fst p ≟ fst q


-- BPureBraid→BPureBraid' n (threeGenCommutativityMiddle r p q proof-rp proof-pq i j) | (lt proof) with fst r ≟ fst p
-- BPureBraid→BPureBraid' n (threeGenCommutativityMiddle r p q proof-rp proof-pq i j) | (lt proof) | (lt proof2) with fst r ≟ fst q
-- BPureBraid→BPureBraid' n (threeGenCommutativityMiddle r p q proof-rp proof-pq i j) | (lt proof) | (lt proof2) | (lt proof3) =  threeGenCommutativityMiddle r p q proof2 proof proof3 i j  -- threeGenCommutativityMiddle r p q proof-rp proof-pq proof3 i {! j !} -- 1st possible case
-- BPureBraid→BPureBraid' n (threeGenCommutativityMiddle r p q proof-rp proof-pq i j) | (lt proof) | (lt proof2) | (eq proof3) =  ⊥.rec {A = Square (gen r p proof2 ) (sym (gen p q proof)) refl refl} ( <!= (trans proof-rp proof-pq) proof3  ) i j
-- BPureBraid→BPureBraid' n (threeGenCommutativityMiddle r p q proof-rp proof-pq i j) | (lt proof) | (lt proof2) | (gt proof3) =  ⊥.rec {A = Square (gen r p proof2 ) (sym (gen p q proof)) refl (gen q r proof3)} (asym proof3 (weaken (trans proof-rp proof-pq))) i j --⊥.rec {A = Square (gen p q proof) (sym(gen q r proof3)) refl (gen r p proof2)} (asym (trans proof-rp proof-pq) (weaken proof3)) i j 


-- BPureBraid→BPureBraid' n (threeGenCommutativityMiddle r p q proof-rp proof-pq i j) | (lt proof) | (eq proof2) with fst r ≟ fst q
-- BPureBraid→BPureBraid' n (threeGenCommutativityMiddle r p q proof-rp proof-pq i j) | (lt proof) | (eq proof2) | (lt proof3) =  ⊥.rec {A = Square refl (sym (gen p q proof)) refl (gen r q proof3)} (<!= proof-rp proof2) i j 
-- BPureBraid→BPureBraid' n (threeGenCommutativityMiddle r p q proof-rp proof-pq i j) | (lt proof) | (eq proof2) | (eq proof3) =  ⊥.rec {A = Square refl (sym (gen p q proof)) refl refl} (<!= proof-rp proof2) i j
-- BPureBraid→BPureBraid' n (threeGenCommutativityMiddle r p q proof-rp proof-pq i j) | (lt proof) | (eq proof2) | (gt proof3) =  ⊥.rec {A = Square refl (sym (gen p q proof)) refl (gen q r proof3)} (<!= proof-rp proof2) i j 


-- BPureBraid→BPureBraid' n (threeGenCommutativityMiddle r p q proof-rp proof-pq i j) | (lt proof) | (gt proof2) with fst r ≟ fst q 
-- BPureBraid→BPureBraid' n (threeGenCommutativityMiddle r p q proof-rp proof-pq i j) | (lt proof) | (gt proof2) | (lt proof3) =  ⊥.rec {A = Square (gen p r proof2) (sym (gen p q proof)) refl (gen r q proof3)} (asym proof2 (weaken proof-rp)) i j 
-- BPureBraid→BPureBraid' n (threeGenCommutativityMiddle r p q proof-rp proof-pq i j) | (lt proof) | (gt proof2) | (eq proof3) =  ⊥.rec {A = Square (gen p r proof2) (sym (gen p q proof)) refl refl} (asym proof2 (weaken proof-rp)) i j 
-- BPureBraid→BPureBraid' n (threeGenCommutativityMiddle r p q proof-rp proof-pq i j) | (lt proof) | (gt proof2) | (gt proof3) =  ⊥.rec {A = Square (gen p r proof2) (sym (gen p q proof)) refl (gen q r proof3)} (asym proof2 (weaken proof-rp)) i j 



-- BPureBraid→BPureBraid' n (threeGenCommutativityMiddle r p q proof-rp proof-pq i j) | (eq proof) with fst r ≟ fst p
-- BPureBraid→BPureBraid' n (threeGenCommutativityMiddle r p q proof-rp proof-pq i j) | (eq proof) | (lt proof2) with fst r ≟ fst q
-- BPureBraid→BPureBraid' n (threeGenCommutativityMiddle r p q proof-rp proof-pq i j) | (eq proof) | (lt proof2) | (lt proof3) =  ⊥.rec {A = Square (gen r p proof2) refl refl (gen r q proof3)} (<!= proof-pq proof) i j 
-- BPureBraid→BPureBraid' n (threeGenCommutativityMiddle r p q proof-rp proof-pq i j) | (eq proof) | (lt proof2) | (eq proof3) =  ⊥.rec {A = Square (gen r p proof2) refl refl refl} (<!= proof-pq proof) i j  
-- BPureBraid→BPureBraid' n (threeGenCommutativityMiddle r p q proof-rp proof-pq i j) | (eq proof) | (lt proof2) | (gt proof3) =  ⊥.rec {A = Square (gen r p proof2) refl refl (gen q r proof3)} (<!= proof-pq proof) i j 

-- BPureBraid→BPureBraid' n (threeGenCommutativityMiddle r p q proof-rp proof-pq i j) | (eq proof) | (eq proof2) with fst r ≟ fst q
-- BPureBraid→BPureBraid' n (threeGenCommutativityMiddle r p q proof-rp proof-pq i j) | (eq proof) | (eq proof2) | (lt proof3) =   ⊥.rec {A = Square refl refl refl (gen r q proof3)} (<!= proof-pq proof) i j  
-- BPureBraid→BPureBraid' n (threeGenCommutativityMiddle r p q proof-rp proof-pq i j) | (eq proof) | (eq proof2) | (eq proof3) =  base 
-- BPureBraid→BPureBraid' n (threeGenCommutativityMiddle r p q proof-rp proof-pq i j) | (eq proof) | (eq proof2) | (gt proof3) =   ⊥.rec {A = Square refl refl refl (gen q r proof3)} (<!= proof-pq proof) i j  

-- BPureBraid→BPureBraid' n (threeGenCommutativityMiddle r p q proof-rp proof-pq i j) | (eq proof) | (gt proof2) with fst r ≟ fst q
-- BPureBraid→BPureBraid' n (threeGenCommutativityMiddle r p q proof-rp proof-pq i j) | (eq proof) | (gt proof2) | (lt proof3) =  ⊥.rec {A = Square (gen p r proof2) refl refl (gen r q proof3)} (<!= proof-pq proof) i j
-- BPureBraid→BPureBraid' n (threeGenCommutativityMiddle r p q proof-rp proof-pq i j) | (eq proof) | (gt proof2) | (eq proof3) =  ⊥.rec {A = Square (gen p r proof2) refl refl refl} (<!= proof-pq proof) i j 
-- BPureBraid→BPureBraid' n (threeGenCommutativityMiddle r p q proof-rp proof-pq i j) | (eq proof) | (gt proof2) | (gt proof3) =  ⊥.rec {A = Square (gen p r proof2) refl refl (gen q r proof3)} (<!= proof-pq proof) i j 



-- BPureBraid→BPureBraid' n (threeGenCommutativityMiddle r p q proof-rp proof-pq i j) | (gt proof) with fst r ≟ fst p 
-- BPureBraid→BPureBraid' n (threeGenCommutativityMiddle r p q proof-rp proof-pq i j) | (gt proof) | (lt proof2) with fst r ≟ fst q
-- BPureBraid→BPureBraid' n (threeGenCommutativityMiddle r p q proof-rp proof-pq i j) | (gt proof) | (lt proof2) | (lt proof3) =  ⊥.rec {A = Square (gen r p proof2) (sym (gen q p proof)) refl (gen r q proof3)} (asym proof (weaken proof-pq)) i j 
-- BPureBraid→BPureBraid' n (threeGenCommutativityMiddle r p q proof-rp proof-pq i j) | (gt proof) | (lt proof2) | (eq proof3) =  ⊥.rec {A = Square (gen r p proof2) (sym (gen q p proof)) refl refl} (asym proof (weaken proof-pq)) i j 
-- BPureBraid→BPureBraid' n (threeGenCommutativityMiddle r p q proof-rp proof-pq i j) | (gt proof) | (lt proof2) | (gt proof3) =  ⊥.rec {A = Square (gen r p proof2) (sym (gen q p proof)) refl (gen q r proof3)} (asym proof (weaken proof-pq)) i j 

-- BPureBraid→BPureBraid' n (threeGenCommutativityMiddle r p q proof-rp proof-pq i j) | (gt proof) | (eq proof2) with fst r ≟ fst q
-- BPureBraid→BPureBraid' n (threeGenCommutativityMiddle r p q proof-rp proof-pq i j) | (gt proof) | (eq proof2) | (lt proof3) =  ⊥.rec {A = Square refl (sym (gen q p proof)) refl (gen r q proof3)} (<!= proof-rp proof2) i j 
-- BPureBraid→BPureBraid' n (threeGenCommutativityMiddle r p q proof-rp proof-pq i j) | (gt proof) | (eq proof2) | (eq proof3) =  ⊥.rec {A = Square refl (sym (gen q p proof)) refl refl} (<!= proof-rp proof2) i j
-- BPureBraid→BPureBraid' n (threeGenCommutativityMiddle r p q proof-rp proof-pq i j) | (gt proof) | (eq proof2) | (gt proof3) =  ⊥.rec {A = Square refl (sym (gen q p proof)) refl (gen q r proof3)} (<!= proof-rp proof2) i j

-- BPureBraid→BPureBraid' n (threeGenCommutativityMiddle r p q proof-rp proof-pq i j) | (gt proof) | (gt proof2) with fst r ≟ fst q
-- BPureBraid→BPureBraid' n (threeGenCommutativityMiddle r p q proof-rp proof-pq i j) | (gt proof) | (gt proof2) | (lt proof3) =  ⊥.rec {A = Square (gen p r proof2) (sym (gen q p proof)) refl (gen r q proof3)} (asym proof (weaken proof-pq)) i j 
-- BPureBraid→BPureBraid' n (threeGenCommutativityMiddle r p q proof-rp proof-pq i j) | (gt proof) | (gt proof2) | (eq proof3) =  ⊥.rec {A = Square (gen p r proof2) (sym (gen q p proof)) refl refl} ((asym proof (weaken proof-pq))) i j 
-- BPureBraid→BPureBraid' n (threeGenCommutativityMiddle r p q proof-rp proof-pq i j) | (gt proof) | (gt proof2) | (gt proof3) =  ⊥.rec {A = Square (gen p r proof2) (sym (gen q p proof)) refl (gen q r proof3)} ((asym proof (weaken proof-pq))) i j 

-- -------------------------------------------------------------------------------------------------------------------------------------------

-- BPureBraid→BPureBraid' n (threeGenCommutativityRight r p q proof-rp proof-pq i j) with fst p ≟ fst q



-- BPureBraid→BPureBraid' n (threeGenCommutativityRight r p q proof-rp proof-pq i j) | (lt proof) with fst r ≟ fst p
-- BPureBraid→BPureBraid' n (threeGenCommutativityRight r p q proof-rp proof-pq i j) | (lt proof) | (lt proof2) with fst r ≟ fst q
-- BPureBraid→BPureBraid' n (threeGenCommutativityRight r p q proof-rp proof-pq i j) | (lt proof) | (lt proof2) | (lt proof3) =  threeGenCommutativityRight r p q proof2 proof proof3 i j 
-- BPureBraid→BPureBraid' n (threeGenCommutativityRight r p q proof-rp proof-pq i j) | (lt proof) | (lt proof2) | (eq proof3) = ⊥.rec {A = Square refl (sym (gen r p proof2)) refl (gen p q proof) } (<!= (trans proof-rp proof-pq) proof3) i j 
-- BPureBraid→BPureBraid' n (threeGenCommutativityRight r p q proof-rp proof-pq i j) | (lt proof) | (lt proof2) | (gt proof3) = ⊥.rec {A = Square (gen q r proof3 ) (sym (gen r p proof2)) refl (gen p q proof)} (asym proof3 (weaken (trans proof-rp proof-pq))) i j 


-- BPureBraid→BPureBraid' n (threeGenCommutativityRight r p q proof-rp proof-pq i j) | (lt proof) | (eq proof2) with fst r ≟ fst q
-- BPureBraid→BPureBraid' n (threeGenCommutativityRight r p q proof-rp proof-pq i j) | (lt proof) | (eq proof2) | (lt proof3) = ⊥.rec {A = Square (gen r q proof3) refl refl (gen p q proof)} (<!= proof-rp proof2) i j 
-- BPureBraid→BPureBraid' n (threeGenCommutativityRight r p q proof-rp proof-pq i j) | (lt proof) | (eq proof2) | (eq proof3) = ⊥.rec {A = Square refl refl refl (gen p q proof)} (<!= proof-rp proof2) i j
-- BPureBraid→BPureBraid' n (threeGenCommutativityRight r p q proof-rp proof-pq i j) | (lt proof) | (eq proof2) | (gt proof3) = ⊥.rec {A = Square (gen q r proof3) refl refl (gen p q proof)} (<!= proof-rp proof2) i j


-- BPureBraid→BPureBraid' n (threeGenCommutativityRight r p q proof-rp proof-pq i j) | (lt proof) | (gt proof2) with fst r ≟ fst q 
-- BPureBraid→BPureBraid' n (threeGenCommutativityRight r p q proof-rp proof-pq i j) | (lt proof) | (gt proof2) | (lt proof3) = ⊥.rec {A = Square (gen r q proof3) (sym (gen p r proof2)) refl (gen p q proof)} (asym proof2 (weaken proof-rp)) i j 
-- BPureBraid→BPureBraid' n (threeGenCommutativityRight r p q proof-rp proof-pq i j) | (lt proof) | (gt proof2) | (eq proof3) = ⊥.rec {A = Square refl (sym (gen p r proof2)) refl (gen p q proof)} (asym proof2 (weaken proof-rp)) i j 
-- BPureBraid→BPureBraid' n (threeGenCommutativityRight r p q proof-rp proof-pq i j) | (lt proof) | (gt proof2) | (gt proof3) = ⊥.rec {A = Square (gen q r proof3) (sym (gen p r proof2)) refl (gen p q proof)} (asym proof2 (weaken proof-rp)) i j 



-- BPureBraid→BPureBraid' n (threeGenCommutativityRight r p q proof-rp proof-pq i j) | (eq proof) with fst r ≟ fst p
-- BPureBraid→BPureBraid' n (threeGenCommutativityRight r p q proof-rp proof-pq i j) | (eq proof) | (lt proof2) with fst r ≟ fst q
-- BPureBraid→BPureBraid' n (threeGenCommutativityRight r p q proof-rp proof-pq i j) | (eq proof) | (lt proof2) | (lt proof3) = ⊥.rec {A = Square (gen r q proof3) (sym (gen r p proof2)) refl refl} (<!= proof-pq proof) i j 
-- BPureBraid→BPureBraid' n (threeGenCommutativityRight r p q proof-rp proof-pq i j) | (eq proof) | (lt proof2) | (eq proof3) =  ⊥.rec {A = Square refl (sym (gen r p proof2)) refl refl} (<!= proof-pq proof) i j   
-- BPureBraid→BPureBraid' n (threeGenCommutativityRight r p q proof-rp proof-pq i j) | (eq proof) | (lt proof2) | (gt proof3) = ⊥.rec {A = Square (gen q r proof3) (sym (gen r p proof2)) refl refl} (<!= proof-pq proof) i j 

-- BPureBraid→BPureBraid' n (threeGenCommutativityRight r p q proof-rp proof-pq i j) | (eq proof) | (eq proof2) with fst r ≟ fst q
-- BPureBraid→BPureBraid' n (threeGenCommutativityRight r p q proof-rp proof-pq i j) | (eq proof) | (eq proof2) | (lt proof3) =  ⊥.rec {A = Square (gen r q proof3) refl refl refl} (<!= proof-pq proof) i j 
-- BPureBraid→BPureBraid' n (threeGenCommutativityRight r p q proof-rp proof-pq i j) | (eq proof) | (eq proof2) | (eq proof3) = base 
-- BPureBraid→BPureBraid' n (threeGenCommutativityRight r p q proof-rp proof-pq i j) | (eq proof) | (eq proof2) | (gt proof3) =  ⊥.rec {A = Square (gen q r proof3) refl refl refl} (<!= proof-pq proof) i j 

-- BPureBraid→BPureBraid' n (threeGenCommutativityRight r p q proof-rp proof-pq i j) | (eq proof) | (gt proof2) with fst r ≟ fst q
-- BPureBraid→BPureBraid' n (threeGenCommutativityRight r p q proof-rp proof-pq i j) | (eq proof) | (gt proof2) | (lt proof3) = ⊥.rec {A = Square (gen r q proof3) (sym (gen p r proof2)) refl refl} (<!= proof-pq proof) i j 
-- BPureBraid→BPureBraid' n (threeGenCommutativityRight r p q proof-rp proof-pq i j) | (eq proof) | (gt proof2) | (eq proof3) =  ⊥.rec {A = Square refl (sym (gen p r proof2)) refl refl} (<!= proof-pq proof) i j  
-- BPureBraid→BPureBraid' n (threeGenCommutativityRight r p q proof-rp proof-pq i j) | (eq proof) | (gt proof2) | (gt proof3) = ⊥.rec {A = Square (gen q r proof3) (sym (gen p r proof2)) refl refl} (<!= proof-pq proof) i j


-- BPureBraid→BPureBraid' n (threeGenCommutativityRight r p q proof-rp proof-pq i j) | (gt proof) with fst r ≟ fst p 
-- BPureBraid→BPureBraid' n (threeGenCommutativityRight r p q proof-rp proof-pq i j) | (gt proof) | (lt proof2) with fst r ≟ fst q
-- BPureBraid→BPureBraid' n (threeGenCommutativityRight r p q proof-rp proof-pq i j) | (gt proof) | (lt proof2) | (lt proof3) = ⊥.rec {A = Square (gen r q proof3) (sym (gen r p proof2)) refl (gen q p proof)} (asym proof (weaken proof-pq)) i j
-- BPureBraid→BPureBraid' n (threeGenCommutativityRight r p q proof-rp proof-pq i j) | (gt proof) | (lt proof2) | (eq proof3) = ⊥.rec {A = Square refl (sym (gen r p proof2)) refl (gen q p proof)} (asym proof (weaken proof-pq)) i j 
-- BPureBraid→BPureBraid' n (threeGenCommutativityRight r p q proof-rp proof-pq i j) | (gt proof) | (lt proof2) | (gt proof3) = ⊥.rec {A = Square (gen q r proof3) (sym (gen r p proof2)) refl (gen q p proof)} (asym proof (weaken proof-pq)) i j 

-- BPureBraid→BPureBraid' n (threeGenCommutativityRight r p q proof-rp proof-pq i j) | (gt proof) | (eq proof2) with fst r ≟ fst q
-- BPureBraid→BPureBraid' n (threeGenCommutativityRight r p q proof-rp proof-pq i j) | (gt proof) | (eq proof2) | (lt proof3) = ⊥.rec {A = Square (gen r q proof3) refl refl (gen q p proof)}  (asym proof (weaken proof-pq)) i j
-- BPureBraid→BPureBraid' n (threeGenCommutativityRight r p q proof-rp proof-pq i j) | (gt proof) | (eq proof2) | (eq proof3) = ⊥.rec {A = Square refl refl refl (gen q p proof)}  (asym proof (weaken proof-pq)) i j
-- BPureBraid→BPureBraid' n (threeGenCommutativityRight r p q proof-rp proof-pq i j) | (gt proof) | (eq proof2) | (gt proof3) = ⊥.rec {A = Square (gen q r proof3) refl refl (gen q p proof)}  (asym proof (weaken proof-pq)) i j

-- BPureBraid→BPureBraid' n (threeGenCommutativityRight r p q proof-rp proof-pq i j) | (gt proof) | (gt proof2) with fst r ≟ fst q
-- BPureBraid→BPureBraid' n (threeGenCommutativityRight r p q proof-rp proof-pq i j) | (gt proof) | (gt proof2) | (lt proof3) = ⊥.rec {A = Square (gen r q proof3) (sym (gen p r proof2)) refl (gen q p proof)}  (asym proof (weaken proof-pq)) i j
-- BPureBraid→BPureBraid' n (threeGenCommutativityRight r p q proof-rp proof-pq i j) | (gt proof) | (gt proof2) | (eq proof3) = ⊥.rec {A = Square refl (sym (gen p r proof2)) refl (gen q p proof)}  (asym proof (weaken proof-pq)) i j 
-- BPureBraid→BPureBraid' n (threeGenCommutativityRight r p q proof-rp proof-pq i j) | (gt proof) | (gt proof2) | (gt proof3) = ⊥.rec {A = Square (gen q r proof3) (sym (gen p r proof2)) refl (gen q p proof)}  (asym proof (weaken proof-pq))     i j 


-- -------------------------------------------------------------------------------------------------------------------------------------------
-- -------------------------------------------------------------------------------------------------------------------------------------------

-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i)  with fst r ≟ fst s
-- -------------------------------------------------------------------------------------------------------------------------------------------
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (lt proof) with fst r ≟ fst q

-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (lt proof) | (lt proof2) with fst p ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (lt proof) | (lt proof2) | (lt proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (lt proof) | (lt proof2) | (lt proof3) | (lt proof4) =   fourGenCommutativityConnector r p s q proof-rp proof-ps proof4 proof2 proof3 i   -- only possible case
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (lt proof) | (lt proof2) | (lt proof3) | (eq proof4) =  base   
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (lt proof) | (lt proof2) | (lt proof3) | (gt proof4) =  base 

-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (lt proof) | (lt proof2) | (eq proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (lt proof) | (lt proof2) | (eq proof3) | (lt proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (lt proof) | (lt proof2) | (eq proof3) | (eq proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (lt proof) | (lt proof2) | (eq proof3) | (gt proof4) =  base

-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (lt proof) | (lt proof2) | (gt proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (lt proof) | (lt proof2) | (gt proof3) | (lt proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (lt proof) | (lt proof2) | (gt proof3) | (eq proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (lt proof) | (lt proof2) | (gt proof3) | (gt proof4) =  base 


-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (lt proof) | (eq proof2) with fst p ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (lt proof) | (eq proof2) | (lt proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (lt proof) | (eq proof2) | (lt proof3) | (lt proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (lt proof) | (eq proof2) | (lt proof3) | (eq proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (lt proof) | (eq proof2) | (lt proof3) | (gt proof4) =  base 

-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (lt proof) | (eq proof2) | (eq proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (lt proof) | (eq proof2) | (eq proof3) | (lt proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (lt proof) | (eq proof2) | (eq proof3) | (eq proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (lt proof) | (eq proof2) | (eq proof3) | (gt proof4) =  base

-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (lt proof) | (eq proof2) | (gt proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (lt proof) | (eq proof2) | (gt proof3) | (lt proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (lt proof) | (eq proof2) | (gt proof3) | (eq proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (lt proof) | (eq proof2) | (gt proof3) | (gt proof4) =  base 

-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (lt proof) | (gt proof2) with fst p ≟ fst q 
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (lt proof) | (gt proof2) | (lt proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (lt proof) | (gt proof2) | (lt proof3) | (lt proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (lt proof) | (gt proof2) | (lt proof3) | (eq proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (lt proof) | (gt proof2) | (lt proof3) | (gt proof4) =  base 

-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (lt proof) | (gt proof2) | (eq proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (lt proof) | (gt proof2) | (eq proof3) | (lt proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (lt proof) | (gt proof2) | (eq proof3) | (eq proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (lt proof) | (gt proof2) | (eq proof3) | (gt proof4) =  base 

-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (lt proof) | (gt proof2) | (gt proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (lt proof) | (gt proof2) | (gt proof3) | (lt proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (lt proof) | (gt proof2) | (gt proof3) | (eq proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (lt proof) | (gt proof2) | (gt proof3) | (gt proof4) =  base 



-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (eq proof) with fst r ≟ fst q


-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (eq proof) | (lt proof2) with fst p ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (eq proof) | (lt proof2) | (lt proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (eq proof) | (lt proof2) | (lt proof3) | (lt proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (eq proof) | (lt proof2) | (lt proof3) | (eq proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (eq proof) | (lt proof2) | (lt proof3) | (gt proof4) =  base 

-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (eq proof) | (lt proof2) | (eq proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (eq proof) | (lt proof2) | (eq proof3) | (lt proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (eq proof) | (lt proof2) | (eq proof3) | (eq proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (eq proof) | (lt proof2) | (eq proof3) | (gt proof4) =  base 

-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (eq proof) | (lt proof2) | (gt proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (eq proof) | (lt proof2) | (gt proof3) | (lt proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (eq proof) | (lt proof2) | (gt proof3) | (eq proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (eq proof) | (lt proof2) | (gt proof3) | (gt proof4) =  base 


-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (eq proof) | (eq proof2) with fst p ≟ fst q

-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (eq proof) | (eq proof2) | (lt proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (eq proof) | (eq proof2) | (lt proof3) | (lt proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (eq proof) | (eq proof2) | (lt proof3) | (eq proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (eq proof) | (eq proof2) | (lt proof3) | (gt proof4) =  base

-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (eq proof) | (eq proof2) | (eq proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (eq proof) | (eq proof2) | (eq proof3) | (lt proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (eq proof) | (eq proof2) | (eq proof3) | (eq proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (eq proof) | (eq proof2) | (eq proof3) | (gt proof4) =  base

-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (eq proof) | (eq proof2) | (gt proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (eq proof) | (eq proof2) | (gt proof3) | (lt proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (eq proof) | (eq proof2) | (gt proof3) | (eq proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (eq proof) | (eq proof2) | (gt proof3) | (gt proof4) =  base


-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (eq proof) | (gt proof2) with fst p ≟ fst q

-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (eq proof) | (gt proof2) | (lt proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (eq proof) | (gt proof2) | (lt proof3) | (lt proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (eq proof) | (gt proof2) | (lt proof3) | (eq proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (eq proof) | (gt proof2) | (lt proof3) | (gt proof4) =  base 

-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (eq proof) | (gt proof2) | (eq proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (eq proof) | (gt proof2) | (eq proof3) | (lt proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (eq proof) | (gt proof2) | (eq proof3) | (eq proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (eq proof) | (gt proof2) | (eq proof3) | (gt proof4) =  base 

-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (eq proof) | (gt proof2) | (gt proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (eq proof) | (gt proof2) | (gt proof3) | (lt proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (eq proof) | (gt proof2) | (gt proof3) | (eq proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (eq proof) | (gt proof2) | (gt proof3) | (gt proof4) =  base 



-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (gt proof) with fst r ≟ fst q

-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (gt proof) | (lt proof2) with fst p ≟ fst q

-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (gt proof) | (lt proof2) | (lt proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (gt proof) | (lt proof2) | (lt proof3) | (lt proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (gt proof) | (lt proof2) | (lt proof3) | (eq proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (gt proof) | (lt proof2) | (lt proof3) | (gt proof4) =  base 

-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (gt proof) | (lt proof2) | (eq proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (gt proof) | (lt proof2) | (eq proof3) | (lt proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (gt proof) | (lt proof2) | (eq proof3) | (eq proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (gt proof) | (lt proof2) | (eq proof3) | (gt proof4) =  base 

-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (gt proof) | (lt proof2) | (gt proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (gt proof) | (lt proof2) | (gt proof3) | (lt proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (gt proof) | (lt proof2) | (gt proof3) | (eq proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (gt proof) | (lt proof2) | (gt proof3) | (gt proof4) =  base 

-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (gt proof) | (eq proof2) with fst p ≟ fst q

-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (gt proof) | (eq proof2) | (lt proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (gt proof) | (eq proof2) | (lt proof3) | (lt proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (gt proof) | (eq proof2) | (lt proof3) | (eq proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (gt proof) | (eq proof2) | (lt proof3) | (gt proof4) =  base 

-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (gt proof) | (eq proof2) | (eq proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (gt proof) | (eq proof2) | (eq proof3) | (lt proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (gt proof) | (eq proof2) | (eq proof3) | (eq proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (gt proof) | (eq proof2) | (eq proof3) | (gt proof4) =  base

-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (gt proof) | (eq proof2) | (gt proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (gt proof) | (eq proof2) | (gt proof3) | (lt proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (gt proof) | (eq proof2) | (gt proof3) | (eq proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (gt proof) | (eq proof2) | (gt proof3) | (gt proof4) =  base 

-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (gt proof) | (gt proof2) with fst p ≟ fst q

-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (gt proof) | (gt proof2) | (lt proof3) with fst s ≟ fst q

-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (gt proof) | (gt proof2) | (lt proof3) | (lt proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (gt proof) | (gt proof2) | (lt proof3) | (eq proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (gt proof) | (gt proof2) | (lt proof3) | (gt proof4) =  base

-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (gt proof) | (gt proof2) | (eq proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (gt proof) | (gt proof2) | (eq proof3) | (lt proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (gt proof) | (gt proof2) | (eq proof3) | (eq proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (gt proof) | (gt proof2) | (eq proof3) | (gt proof4) =  base 

-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (gt proof) | (gt proof2) | (gt proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (gt proof) | (gt proof2) | (gt proof3) | (lt proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (gt proof) | (gt proof2) | (gt proof3) | (eq proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) | (gt proof) | (gt proof2) | (gt proof3) | (gt proof4) =  base 







-- -------------------------------------------------------------------------------------------------------------------------------------------






-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j)  with fst r ≟ fst s
-- -------------------------------------------------------------------------------------------------------------------------------------------
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (lt proof) with fst r ≟ fst q

-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (lt proof2) with fst p ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (lt proof2) | (lt proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (lt proof2) | (lt proof3) | (lt proof4) =   fourGenCommutativityComposition r p s q proof-rp proof-ps  proof4 proof2 proof3 i j  -- only possible case
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (lt proof2) | (lt proof3) | (eq proof4) =   ⊥.rec {A = Square (gen r q proof2) refl refl (gen p q proof3)} (<!= proof-sq proof4) i j   
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (lt proof2) | (lt proof3) | (gt proof4) =   ⊥.rec {A = Square (gen r q proof2) (sym (gen q s proof4)) refl (gen p q proof3)} (asym proof4 (weaken proof-sq)) i j    

-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (lt proof2) | (eq proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (lt proof2) | (eq proof3) | (lt proof4) =   ⊥.rec {A = Square (gen r q proof2) (sym (gen s q  proof4)) refl refl} (<!= (trans proof-ps proof-sq) proof3) i j  
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (lt proof2) | (eq proof3) | (eq proof4) =   ⊥.rec {A = Square (gen r q proof2) refl refl refl } (<!= (trans proof-ps proof-sq) proof3) i j  
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (lt proof2) | (eq proof3) | (gt proof4) =   ⊥.rec {A = Square (gen r q proof2) (sym (gen q s  proof4)) refl refl} (<!= (trans proof-ps proof-sq) proof3) i j  

-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (lt proof2) | (gt proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (lt proof2) | (gt proof3) | (lt proof4) =   ⊥.rec {A = Square (gen r q proof2) (sym (gen s q  proof4)) refl (gen q p proof3)} (asym proof3 (weaken (trans proof-ps proof-sq))) i j  
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (lt proof2) | (gt proof3) | (eq proof4) =   ⊥.rec {A = Square (gen r q proof2) refl refl (gen q p proof3)} (asym proof3 (weaken (trans proof-ps proof-sq))) i j  
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (lt proof2) | (gt proof3) | (gt proof4) =   ⊥.rec {A = Square (gen r q proof2) (sym (gen q s  proof4)) refl (gen q p proof3) } (asym proof3 (weaken (trans proof-ps proof-sq))) i j   


-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (eq proof2) with fst p ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (eq proof2) | (lt proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (eq proof2) | (lt proof3) | (lt proof4) =  ⊥.rec {A = Square refl (sym (gen s q  proof4)) refl (gen p q proof3)} (<!= (trans proof-rp (trans proof-ps proof-sq)) proof2) i j 
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (eq proof2) | (lt proof3) | (eq proof4) =  ⊥.rec {A = Square refl refl refl (gen p q proof3)} (<!= (trans proof-rp (trans proof-ps proof-sq)) proof2) i j 
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (eq proof2) | (lt proof3) | (gt proof4) =  ⊥.rec {A = Square refl (sym (gen q s  proof4)) refl (gen p q proof3)} (<!= (trans proof-rp (trans proof-ps proof-sq)) proof2) i j  

-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (eq proof2) | (eq proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (eq proof2) | (eq proof3) | (lt proof4) =  ⊥.rec {A = Square refl (sym (gen s q proof4)) refl refl} (<!= (trans proof-rp (trans proof-ps proof-sq)) proof2) i j
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (eq proof2) | (eq proof3) | (eq proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (eq proof2) | (eq proof3) | (gt proof4) =  ⊥.rec {A = Square refl (sym (gen q s  proof4)) refl refl} (<!= (trans proof-rp (trans proof-ps proof-sq)) proof2) i j   

-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (eq proof2) | (gt proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (eq proof2) | (gt proof3) | (lt proof4) =  ⊥.rec {A = Square refl (sym (gen s q  proof4)) refl (gen q p proof3)} (<!= (trans proof-rp (trans proof-ps proof-sq)) proof2) i j 
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (eq proof2) | (gt proof3) | (eq proof4) =  ⊥.rec {A = Square refl refl  refl (gen q p proof3)} (<!= proof-sq proof4) i j 
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (eq proof2) | (gt proof3) | (gt proof4) =  ⊥.rec {A = Square refl (sym (gen q s  proof4)) refl (gen q p proof3)} (<!= (trans proof-rp (trans proof-ps proof-sq)) proof2) i j  

-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (gt proof2) with fst p ≟ fst q 
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (gt proof2) | (lt proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (gt proof2) | (lt proof3) | (lt proof4) =  ⊥.rec {A = Square (gen q r proof2) (sym (gen s q  proof4)) refl (gen p q  proof3)} (asym proof2 (weaken (trans proof-rp (trans proof-ps proof-sq)))) i j 
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (gt proof2) | (lt proof3) | (eq proof4) =  ⊥.rec {A = Square (gen q r proof2) refl refl (gen p q  proof3)} (asym proof2 (weaken (trans proof-rp (trans proof-ps proof-sq)))) i j 
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (gt proof2) | (lt proof3) | (gt proof4) =  ⊥.rec {A = Square (gen q r proof2) (sym (gen q s  proof4)) refl (gen p q proof3)} (asym proof2 (weaken (trans proof-rp (trans proof-ps proof-sq)))) i j  

-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (gt proof2) | (eq proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (gt proof2) | (eq proof3) | (lt proof4) =  ⊥.rec {A = Square (gen q r proof2) (sym (gen s q  proof4)) refl refl} (asym proof2 (weaken (trans proof-rp (trans proof-ps proof-sq)))) i j  
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (gt proof2) | (eq proof3) | (eq proof4) =  ⊥.rec {A = Square (gen q r proof2) refl refl refl} (asym proof2 (weaken (trans proof-rp (trans proof-ps proof-sq)))) i j  
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (gt proof2) | (eq proof3) | (gt proof4) =  ⊥.rec {A = Square (gen q r proof2) (sym (gen q s  proof4)) refl refl} (asym proof2 (weaken (trans proof-rp (trans proof-ps proof-sq)))) i j   

-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (gt proof2) | (gt proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (gt proof2) | (gt proof3) | (lt proof4) =  ⊥.rec {A = Square (gen q r proof2) (sym (gen s q  proof4)) refl (gen q p proof3)} (asym proof2 (weaken (trans proof-rp (trans proof-ps proof-sq)))) i j  
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (gt proof2) | (gt proof3) | (eq proof4) =  ⊥.rec {A = Square (gen q r proof2) refl refl (gen q p proof3)} (asym proof2 (weaken (trans proof-rp (trans proof-ps proof-sq)))) i j  
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (gt proof2) | (gt proof3) | (gt proof4) =  ⊥.rec {A = Square (gen q r proof2) (sym (gen q s  proof4)) refl (gen q p proof3)} (asym proof2 (weaken (trans proof-rp (trans proof-ps proof-sq)))) i j   



-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (eq proof) with fst r ≟ fst q


-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (lt proof2) with fst p ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (lt proof2) | (lt proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (lt proof2) | (lt proof3) | (lt proof4) =  ⊥.rec {A = Square (gen r q proof2) (sym (gen s q  proof4)) refl (gen p q proof3)} (<!= (trans proof-rp proof-ps) proof) i j  
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (lt proof2) | (lt proof3) | (eq proof4) =  ⊥.rec {A = Square (gen r q proof2) refl  refl (gen p q proof3)} (<!= (trans proof-rp proof-ps) proof) i j
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (lt proof2) | (lt proof3) | (gt proof4) =  ⊥.rec {A = Square (gen r q  proof2) (sym (gen q s  proof4)) refl (gen p q proof3)} (<!= (trans proof-rp proof-ps) proof) i j   

-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (lt proof2) | (eq proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (lt proof2) | (eq proof3) | (lt proof4) =  ⊥.rec {A = Square (gen r q  proof2) (sym (gen s q  proof4)) refl refl} (<!= (trans proof-rp proof-ps) proof) i j  
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (lt proof2) | (eq proof3) | (eq proof4) =  ⊥.rec {A = Square (gen r q  proof2) refl refl refl} (<!= proof-sq proof4) i j  
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (lt proof2) | (eq proof3) | (gt proof4) =  ⊥.rec {A = Square (gen r q proof2) (sym (gen q s  proof4)) refl refl} (<!= (trans proof-rp proof-ps) proof) i j   

-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (lt proof2) | (gt proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (lt proof2) | (gt proof3) | (lt proof4) =  ⊥.rec {A = Square (gen r q proof2) (sym (gen s q  proof4)) refl (gen q p proof3)} (<!= (trans proof-rp proof-ps) proof) i j  
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (lt proof2) | (gt proof3) | (eq proof4) =  ⊥.rec {A = Square (gen r q proof2) refl  refl (gen q p proof3)} (<!= proof-sq proof4) i j  
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (lt proof2) | (gt proof3) | (gt proof4) =  ⊥.rec {A = Square (gen r q proof2) (sym (gen q s  proof4)) refl (gen q p proof3)} (<!= (trans proof-rp proof-ps) proof) i j   


-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (eq proof2) with fst p ≟ fst q

-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (eq proof2) | (lt proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (eq proof2) | (lt proof3) | (lt proof4) =  ⊥.rec {A = Square refl (sym (gen s q  proof4)) refl (gen p q proof3)} (<!= (trans proof-rp proof-ps) proof) i j   
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (eq proof2) | (lt proof3) | (eq proof4) =   ⊥.rec {A = Square refl refl refl (gen p q proof3)} (<!= (trans proof-rp proof-ps) proof) i j      
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (eq proof2) | (lt proof3) | (gt proof4) =   ⊥.rec {A = Square refl (sym (gen q s  proof4)) refl (gen p q proof3)} (<!= (trans proof-rp proof-ps) proof) i j     

-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (eq proof2) | (eq proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (eq proof2) | (eq proof3) | (lt proof4) =   ⊥.rec {A = Square refl (sym (gen s q  proof4)) refl refl} (<!= (trans proof-rp proof-ps) proof) i j      
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (eq proof2) | (eq proof3) | (eq proof4) =   base      
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (eq proof2) | (eq proof3) | (gt proof4) =   ⊥.rec {A = Square refl (sym (gen q s  proof4)) refl refl} (<!= (trans proof-rp proof-ps) proof) i j   

-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (eq proof2) | (gt proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (eq proof2) | (gt proof3) | (lt proof4) =   ⊥.rec {A = Square refl (sym (gen s q  proof4)) refl (gen q p proof3)} (<!= (trans proof-rp proof-ps) proof) i j      
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (eq proof2) | (gt proof3) | (eq proof4) =   ⊥.rec {A = Square refl refl refl (gen q p proof3)} (<!= (trans proof-rp proof-ps) proof) i j   
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (eq proof2) | (gt proof3) | (gt proof4) =   ⊥.rec {A = Square refl (sym (gen q s  proof4)) refl (gen q p proof3)} (<!= (trans proof-rp proof-ps) proof) i j    


-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (gt proof2) with fst p ≟ fst q

-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (gt proof2) | (lt proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (gt proof2) | (lt proof3) | (lt proof4) =   ⊥.rec {A = Square (gen q r proof2) (sym (gen s q  proof4)) refl (gen p q proof3)} (<!= (trans proof-rp proof-ps) proof) i j
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (gt proof2) | (lt proof3) | (eq proof4) =   ⊥.rec {A = Square (gen q r proof2) refl  refl (gen p q proof3)} (<!= (trans proof-rp proof-ps) proof) i j
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (gt proof2) | (lt proof3) | (gt proof4) =   ⊥.rec {A = Square (gen q r proof2) (sym (gen q s  proof4)) refl (gen p q proof3)} (<!= (trans proof-rp proof-ps) proof) i j 

-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (gt proof2) | (eq proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (gt proof2) | (eq proof3) | (lt proof4) =   ⊥.rec {A = Square (gen q r proof2) (sym (gen s q  proof4)) refl refl} (<!= (trans proof-rp proof-ps) proof) i j
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (gt proof2) | (eq proof3) | (eq proof4) =    ⊥.rec {A = Square (gen q r proof2) refl refl refl} (<!= (trans proof-rp proof-ps) proof) i j
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (gt proof2) | (eq proof3) | (gt proof4) =    ⊥.rec {A = Square (gen q r proof2) (sym (gen q s  proof4)) refl refl} (<!= (trans proof-rp proof-ps) proof) i j 

-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (gt proof2) | (gt proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (gt proof2) | (gt proof3) | (lt proof4) =   ⊥.rec {A = Square (gen q r proof2) (sym (gen s q  proof4)) refl (gen q p proof3)} (<!= (trans proof-rp proof-ps) proof) i j
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (gt proof2) | (gt proof3) | (eq proof4) =   ⊥.rec {A = Square (gen q r proof2) refl refl (gen q p proof3)} (<!= (trans proof-rp proof-ps) proof) i j
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (gt proof2) | (gt proof3) | (gt proof4) =   ⊥.rec {A = Square (gen q r proof2) (sym (gen q s  proof4)) refl (gen q p proof3)} (<!= (trans proof-rp proof-ps) proof) i j 



-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (gt proof) with fst r ≟ fst q

-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (lt proof2) with fst p ≟ fst q

-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (lt proof2) | (lt proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (lt proof2) | (lt proof3) | (lt proof4) =  ⊥.rec {A = Square (gen r q proof2) (sym (gen s q  proof4)) refl (gen p q proof3)} (asym proof (weaken (trans proof-rp proof-ps))) i j
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (lt proof2) | (lt proof3) | (eq proof4) =  ⊥.rec {A = Square (gen r q proof2) refl refl (gen p q proof3)} ( asym proof (weaken (trans proof-rp proof-ps))) i j
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (lt proof2) | (lt proof3) | (gt proof4) =  ⊥.rec {A = Square (gen r q proof2) (sym (gen q s proof4)) refl (gen p q proof3)} ( asym proof (weaken (trans proof-rp proof-ps))) i j 

-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (lt proof2) | (eq proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (lt proof2) | (eq proof3) | (lt proof4) =  ⊥.rec {A = Square (gen r q proof2) (sym (gen s q  proof4)) refl refl} ( asym proof (weaken (trans proof-rp proof-ps))) i j
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (lt proof2) | (eq proof3) | (eq proof4) =  ⊥.rec {A = Square (gen r q proof2) refl refl refl} ( asym proof (weaken (trans proof-rp proof-ps))) i j
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (lt proof2) | (eq proof3) | (gt proof4) =  ⊥.rec {A = Square (gen r q proof2) (sym (gen q s  proof4)) refl refl} ( asym proof (weaken (trans proof-rp proof-ps))) i j 

-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (lt proof2) | (gt proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (lt proof2) | (gt proof3) | (lt proof4) =  ⊥.rec {A = Square (gen r q proof2) (sym (gen s q  proof4)) refl (gen q p proof3)} ( asym proof (weaken (trans proof-rp proof-ps))) i j
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (lt proof2) | (gt proof3) | (eq proof4) =  ⊥.rec {A = Square (gen r q proof2) refl refl (gen q p proof3)} ( asym proof (weaken (trans proof-rp proof-ps))) i j
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (lt proof2) | (gt proof3) | (gt proof4) =  ⊥.rec {A = Square (gen r q proof2) (sym (gen q s  proof4)) refl (gen q p proof3)} ( asym proof (weaken (trans proof-rp proof-ps))) i j 

-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (eq proof2) with fst p ≟ fst q

-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (eq proof2) | (lt proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (eq proof2) | (lt proof3) | (lt proof4) =  ⊥.rec {A = Square refl (sym (gen s q  proof4)) refl (gen p q proof3)} ( asym proof (weaken (trans proof-rp proof-ps))) i j
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (eq proof2) | (lt proof3) | (eq proof4) =  ⊥.rec {A = Square refl refl refl (gen p q proof3)} ( asym proof (weaken (trans proof-rp proof-ps))) i j
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (eq proof2) | (lt proof3) | (gt proof4) =  ⊥.rec {A = Square refl (sym (gen q s  proof4)) refl (gen p q proof3)} ( asym proof (weaken (trans proof-rp proof-ps))) i j 

-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (eq proof2) | (eq proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (eq proof2) | (eq proof3) | (lt proof4) =  ⊥.rec {A = Square refl (sym (gen s q  proof4)) refl refl} ( asym proof (weaken (trans proof-rp proof-ps))) i j
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (eq proof2) | (eq proof3) | (eq proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (eq proof2) | (eq proof3) | (gt proof4) =  ⊥.rec {A = Square refl (sym (gen q s  proof4)) refl refl} ( asym proof (weaken (trans proof-rp proof-ps))) i j

-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (eq proof2) | (gt proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (eq proof2) | (gt proof3) | (lt proof4) =  ⊥.rec {A = Square refl (sym (gen s q  proof4)) refl (gen q p proof3)} ( asym proof (weaken (trans proof-rp proof-ps))) i j
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (eq proof2) | (gt proof3) | (eq proof4) =  ⊥.rec {A = Square refl refl refl (gen q p proof3)} ( asym proof (weaken (trans proof-rp proof-ps))) i j
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (eq proof2) | (gt proof3) | (gt proof4) =  ⊥.rec {A = Square refl (sym (gen q s  proof4)) refl (gen q p proof3)} ( asym proof (weaken (trans proof-rp proof-ps))) i j 

-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (gt proof2) with fst p ≟ fst q

-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (gt proof2) | (lt proof3) with fst s ≟ fst q

-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (gt proof2) | (lt proof3) | (lt proof4) =   ⊥.rec {A = Square (gen q r proof2) (sym (gen s q  proof4)) refl (gen p q proof3)} ( asym proof (weaken (trans proof-rp proof-ps))) i j
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (gt proof2) | (lt proof3) | (eq proof4) =   ⊥.rec {A = Square (gen q r proof2) refl refl (gen p q proof3)} ( asym proof (weaken (trans proof-rp proof-ps))) i j 
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (gt proof2) | (lt proof3) | (gt proof4) =     ⊥.rec {A = Square (gen q r proof2) (sym (gen q s  proof4)) refl (gen p q proof3)} ( asym proof (weaken (trans proof-rp proof-ps))) i j

-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (gt proof2) | (eq proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (gt proof2) | (eq proof3) | (lt proof4) =   ⊥.rec {A = Square (gen q r proof2) (sym (gen s q  proof4)) refl refl} ( asym proof (weaken (trans proof-rp proof-ps))) i j
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (gt proof2) | (eq proof3) | (eq proof4) =    ⊥.rec {A = Square (gen q r proof2) refl refl refl } ( asym proof (weaken (trans proof-rp proof-ps))) i j
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (gt proof2) | (eq proof3) | (gt proof4) =    ⊥.rec {A = Square (gen q r proof2) (sym (gen q s  proof4)) refl refl} ( asym proof (weaken (trans proof-rp proof-ps))) i j 

-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (gt proof2) | (gt proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (gt proof2) | (gt proof3) | (lt proof4) =   ⊥.rec {A = Square (gen q r proof2) (sym (gen s q  proof4)) refl (gen q p proof3)} ( asym proof (weaken (trans proof-rp proof-ps))) i j
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (gt proof2) | (gt proof3) | (eq proof4) =  ⊥.rec {A = Square (gen q r proof2) refl refl (gen q p proof3)} ( asym proof (weaken (trans proof-rp proof-ps))) i j
-- BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (gt proof2) | (gt proof3) | (gt proof4) =   ⊥.rec {A = Square (gen q r proof2) (sym (gen q s  proof4)) refl (gen q p proof3)} ( asym proof (weaken (trans proof-rp proof-ps))) i j  

-- -------------------------------------------------------------------------------------------------------------------------------------------

-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) with fst r ≟ fst s
-- -------------------------------------------------------------------------------------------------------------------------------------------
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (lt proof) with fst r ≟ fst q

-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (lt proof2) with fst p ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (lt proof2) | (lt proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (lt proof2) | (lt proof3) | (lt proof4) =    fourGenCommutativity r p s q proof-rp proof-ps proof4 proof proof2 proof3 i j -- only possible case
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (lt proof2) | (lt proof3) | (eq proof4) =  gen r s proof j
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (lt proof2) | (lt proof3) | (gt proof4) =  gen r s proof j

-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (lt proof2) | (eq proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (lt proof2) | (eq proof3) | (lt proof4) =  gen r s proof j
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (lt proof2) | (eq proof3) | (eq proof4) =  gen r s proof j
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (lt proof2) | (eq proof3) | (gt proof4) =  gen r s proof j

-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (lt proof2) | (gt proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (lt proof2) | (gt proof3) | (lt proof4) =  gen r s proof j
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (lt proof2) | (gt proof3) | (eq proof4) =  gen r s proof j
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (lt proof2) | (gt proof3) | (gt proof4) =  gen r s proof j


-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (eq proof2) with fst p ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (eq proof2) | (lt proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (eq proof2) | (lt proof3) | (lt proof4) = gen r s proof j
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (eq proof2) | (lt proof3) | (eq proof4) = gen r s proof j
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (eq proof2) | (lt proof3) | (gt proof4) = gen r s proof j

-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (eq proof2) | (eq proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (eq proof2) | (eq proof3) | (lt proof4) = gen r s proof j
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (eq proof2) | (eq proof3) | (eq proof4) = gen r s proof j
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (eq proof2) | (eq proof3) | (gt proof4) = gen r s proof j

-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (eq proof2) | (gt proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (eq proof2) | (gt proof3) | (lt proof4) = gen r s proof j
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (eq proof2) | (gt proof3) | (eq proof4) = gen r s proof j
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (eq proof2) | (gt proof3) | (gt proof4) = gen r s proof j

-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (gt proof2) with fst p ≟ fst q 
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (gt proof2) | (lt proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (gt proof2) | (lt proof3) | (lt proof4) = gen r s proof j
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (gt proof2) | (lt proof3) | (eq proof4) = gen r s proof j
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (gt proof2) | (lt proof3) | (gt proof4) = gen r s proof j

-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (gt proof2) | (eq proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (gt proof2) | (eq proof3) | (lt proof4) = gen r s proof j
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (gt proof2) | (eq proof3) | (eq proof4) = gen r s proof j
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (gt proof2) | (eq proof3) | (gt proof4) = gen r s proof j

-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (gt proof2) | (gt proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (gt proof2) | (gt proof3) | (lt proof4) = gen r s proof j
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (gt proof2) | (gt proof3) | (eq proof4) = gen r s proof j
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (lt proof) | (gt proof2) | (gt proof3) | (gt proof4) = gen r s proof j



-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (eq proof) with fst r ≟ fst q


-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (lt proof2) with fst p ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (lt proof2) | (lt proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (lt proof2) | (lt proof3) | (lt proof4) = base
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (lt proof2) | (lt proof3) | (eq proof4) = base
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (lt proof2) | (lt proof3) | (gt proof4) = base

-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (lt proof2) | (eq proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (lt proof2) | (eq proof3) | (lt proof4) = base
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (lt proof2) | (eq proof3) | (eq proof4) = base
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (lt proof2) | (eq proof3) | (gt proof4) = base

-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (lt proof2) | (gt proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (lt proof2) | (gt proof3) | (lt proof4) = base
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (lt proof2) | (gt proof3) | (eq proof4) = base
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (lt proof2) | (gt proof3) | (gt proof4) = base


-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (eq proof2) with fst p ≟ fst q

-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (eq proof2) | (lt proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (eq proof2) | (lt proof3) | (lt proof4) = base
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (eq proof2) | (lt proof3) | (eq proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (eq proof2) | (lt proof3) | (gt proof4) =  base

-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (eq proof2) | (eq proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (eq proof2) | (eq proof3) | (lt proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (eq proof2) | (eq proof3) | (eq proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (eq proof2) | (eq proof3) | (gt proof4) =  base

-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (eq proof2) | (gt proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (eq proof2) | (gt proof3) | (lt proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (eq proof2) | (gt proof3) | (eq proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (eq proof2) | (gt proof3) | (gt proof4) =  base


-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (gt proof2) with fst p ≟ fst q

-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (gt proof2) | (lt proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (gt proof2) | (lt proof3) | (lt proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (gt proof2) | (lt proof3) | (eq proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (gt proof2) | (lt proof3) | (gt proof4) =  base

-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (gt proof2) | (eq proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (gt proof2) | (eq proof3) | (lt proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (gt proof2) | (eq proof3) | (eq proof4) =   base
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (gt proof2) | (eq proof3) | (gt proof4) =   base

-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (gt proof2) | (gt proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (gt proof2) | (gt proof3) | (lt proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (gt proof2) | (gt proof3) | (eq proof4) =  base
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (eq proof) | (gt proof2) | (gt proof3) | (gt proof4) =  base



-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (gt proof) with fst r ≟ fst q

-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (lt proof2) with fst p ≟ fst q

-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (lt proof2) | (lt proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (lt proof2) | (lt proof3) | (lt proof4) = gen s r proof j
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (lt proof2) | (lt proof3) | (eq proof4) = gen s r proof j
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (lt proof2) | (lt proof3) | (gt proof4) = gen s r proof j

-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (lt proof2) | (eq proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (lt proof2) | (eq proof3) | (lt proof4) = gen s r proof j
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (lt proof2) | (eq proof3) | (eq proof4) = gen s r proof j
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (lt proof2) | (eq proof3) | (gt proof4) = gen s r proof j

-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (lt proof2) | (gt proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (lt proof2) | (gt proof3) | (lt proof4) = gen s r proof j
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (lt proof2) | (gt proof3) | (eq proof4) = gen s r proof j
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (lt proof2) | (gt proof3) | (gt proof4) = gen s r proof j

-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (eq proof2) with fst p ≟ fst q

-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (eq proof2) | (lt proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (eq proof2) | (lt proof3) | (lt proof4) = gen s r proof j
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (eq proof2) | (lt proof3) | (eq proof4) = gen s r proof j
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (eq proof2) | (lt proof3) | (gt proof4) = gen s r proof j

-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (eq proof2) | (eq proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (eq proof2) | (eq proof3) | (lt proof4) = gen s r proof j
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (eq proof2) | (eq proof3) | (eq proof4) = gen s r proof j
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (eq proof2) | (eq proof3) | (gt proof4) = gen s r proof j

-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (eq proof2) | (gt proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (eq proof2) | (gt proof3) | (lt proof4) = gen s r proof j
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (eq proof2) | (gt proof3) | (eq proof4) = gen s r proof j
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (eq proof2) | (gt proof3) | (gt proof4) = gen s r proof j

-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (gt proof2) with fst p ≟ fst q

-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (gt proof2) | (lt proof3) with fst s ≟ fst q

-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (gt proof2) | (lt proof3) | (lt proof4) =  gen s r proof j
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (gt proof2) | (lt proof3) | (eq proof4) =  gen s r proof j
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (gt proof2) | (lt proof3) | (gt proof4) =    gen s r proof j

-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (gt proof2) | (eq proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (gt proof2) | (eq proof3) | (lt proof4) =  gen s r proof j
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (gt proof2) | (eq proof3) | (eq proof4) =   gen s r proof j
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (gt proof2) | (eq proof3) | (gt proof4) =   gen s r proof j

-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (gt proof2) | (gt proof3) with fst s ≟ fst q
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (gt proof2) | (gt proof3) | (lt proof4) =  gen s r proof j
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (gt proof2) | (gt proof3) | (eq proof4) = gen s r proof j
-- BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) | (gt proof) | (gt proof2) | (gt proof3) | (gt proof4) = gen s r proof j   

-- -------------------------------------------------------------------------------------------------------------------------------------------

