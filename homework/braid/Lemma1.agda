module homework.braid.Lemma1 where
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat.Base
open import Cubical.Data.Fin.Base
open import Cubical.Data.Nat.Order 
open import Cubical.Data.Empty as ⊥


{-
            r ∙∙ p ∙∙ q
          w - - - - - - > z
          ^               ^
    sym r |  ...-filler   | q        ^
          |               |        j |
          x - — — — - - > y          ∙ — >
                  p                    i

-}

{-


         A p q
      b ­- - - > b
      ^         ^
refl  |         |  sym (A s q)
      |         |
      b - - - > b
    refl ·· A p q ·· A s q


-}

lemma1 : {x w y z : Type} {r : w ≡ x}

 