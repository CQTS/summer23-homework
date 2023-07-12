module homework.braid.BraidIsomorphism where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat.Base
open import Cubical.Data.Fin.Base
open import Cubical.Data.Empty as ⊥
open import Cubical.Foundations.Isomorphism 
open import Cubical.Data.Nat.Order renaming (pred-≤-pred to pred)

open import homework.braid.PureBraidAlt
open import homework.braid.PureBraidGroup




BPureBraid→BPureBraid' : ∀ n → (b : BPureBraid n) → BPureBraid' n
BPureBraid→BPureBraid' n base = base
BPureBraid→BPureBraid' n (gen (zero , proof-p) (zero , proof-q) i) = base
BPureBraid→BPureBraid' n (gen (zero , proof-p) (suc q , proof-q) i) = base
BPureBraid→BPureBraid' n (gen (suc p , proof-p) (zero , proof-q) i) = base
BPureBraid→BPureBraid' n (gen (suc zero , proof-p) (suc q , proof-q) i) = {!   !}
BPureBraid→BPureBraid' n (gen (suc (suc p) , proof-p) (suc q , proof-q) i) = {!   !}

BPureBraid→BPureBraid' n (identity (zero , proof-p) i j) = base
BPureBraid→BPureBraid' zero (identity (suc p , proof-p) i j) = {!   !}
BPureBraid→BPureBraid' (suc n) (identity (suc p , proof-p) i j) = {!   !}


BPureBraid→BPureBraid' n (genEquality p q i j) = {!   !}
BPureBraid→BPureBraid' n (twoGenCommutativity1 p q r s proof-rs proof-sp proof-pq i j) = {!   !}
BPureBraid→BPureBraid' n (twoGenCommutativity2 p q r s proof-pr proof-rs proof-sq i j) = {!   !}
BPureBraid→BPureBraid' n (threeGenCommutativityConnector r p q proof-rp proof-pq i) = {!   !}
BPureBraid→BPureBraid' n (threeGenCommutativityLeft r p q proof-rp proof-pq i j) = {!   !}
BPureBraid→BPureBraid' n (threeGenCommutativityMiddle r p q proof-rp proof-pq i j) = {!   !}
BPureBraid→BPureBraid' n (threeGenCommutativityRight r p q proof-rp proof-pq i j) = {!   !}
BPureBraid→BPureBraid' n (fourGenCommutativityConnector r p s q proof-rp proof-ps proof-sq i) = {!   !}
BPureBraid→BPureBraid' n (fourGenCommutativityComposition r p s q proof-rp proof-ps proof-sq i j) = {!   !}
BPureBraid→BPureBraid' n (fourGenCommutativity r p s q proof-rp proof-ps proof-sq i j) = {!   !}





BPureBraid'→BPureBraid : ∀ n → (b : BPureBraid' n) → BPureBraid n 
BPureBraid'→BPureBraid n base = base
BPureBraid'→BPureBraid n (gen p q constraint i) = gen p q i
BPureBraid'→BPureBraid n (commutativity1 p q r s proof-rs proof-sp proof-pq i j) = twoGenCommutativity1 p q r s proof-rs proof-sp proof-pq i j
BPureBraid'→BPureBraid n (commutativity2 p q r s proof-pr proof-rs proof-sq proof-pq i j) = twoGenCommutativity2 p q r s proof-pr proof-rs proof-sq i j
BPureBraid'→BPureBraid n (threewayCommutativityCommon r p q proof-rp proof-pq proof-rq i) = threeGenCommutativityConnector r p q proof-rp proof-pq i
BPureBraid'→BPureBraid n (threewayCommutativityLeft r p q proof-rp proof-pq proof-rq i j) = threeGenCommutativityLeft r p q proof-rp proof-pq {!   !} {!   !}
BPureBraid'→BPureBraid n (threewayCommutativityRight r p q proof-rp proof-pq proof-rq i j) = {!   !}
BPureBraid'→BPureBraid n (threewayCommutativityTop r p q proof-rp proof-pq proof-rq i j) = {!   !}
BPureBraid'→BPureBraid n (fourwayCommutativityConnector r p s q proof-rp proof-ps proof-sq proof-rq proof-pq i) = {!   !}
BPureBraid'→BPureBraid n (fourwayCommutativityComposition r p s q proof-rp proof-ps proof-sq proof-rq proof-pq i j) = {!   !}
BPureBraid'→BPureBraid n (fourwayCommutativity r p s q proof-rp proof-ps proof-sq proof-rs proof-rq proof-pq i j) = {!   !} 






Iso-PBraid-PBraid' : ∀ n →  Iso (BPureBraid n) (BPureBraid' n)
Iso-PBraid-PBraid' n = iso (BPureBraid→BPureBraid' n) (BPureBraid'→BPureBraid n) s r
    where
        s : section (BPureBraid→BPureBraid' n) (BPureBraid'→BPureBraid n)
        s = {!   !}

        r : retract (BPureBraid→BPureBraid' n) (BPureBraid'→BPureBraid n)
        r = {!   !}

