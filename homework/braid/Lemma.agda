module homework.braid.Lemma where
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat.Base
open import Cubical.Data.Fin.Base
open import Cubical.Data.Nat.Order 
open import Cubical.Data.Empty as ⊥


{-

               q
          y - - - > z
          ^         ^
       p  |         | r ∙∙ p ∙∙ q          ^
          |         |                    j |
          x — — — > w                      ∙ — >
             sym r                           i

-}

{-

      r : (sym refl)
      p : A p q
      q : A s q
      

         A p q
      b ­- - - > b
      ^         ^
refl  |         |  sym (A s q)
      |         |
      b - - - > b
    refl ·· A p q ·· A s q

      
          p
      x ­- - - > y
      ^         ^
    r |         | sym q
      |         |
      w - - - > z
      r ·· p ·· q



     x ∙ ∙ ∙ > z
     ‖         ^
     ‖         | r        ^
     ‖         |        j |
     x — — — > y          ∙ — >
          q                 i


       
     x ∙ ∙ ∙ > z
     ‖         ^
     ‖         | A s q    ^
     ‖         |        j |
     x — — — > y          ∙ — >
        A p q               i



-}

lemma1 : {x w y z : Type} {r : w ≡ x} {p : x ≡ y} {q : y ≡ z} (square : Square (sym r) q p (r ∙∙ p ∙∙ q)) → Square (r) (sym q) (r ∙∙ p ∙∙ q) (p)
lemma1 square i j = square i (~ j)

lemma2 : {A : Type} {x w y z : A} {r : w ≡ x} {p : x ≡ y} {q : y ≡ z} (square : Square p (r ∙∙ p ∙∙ q) (sym r) q) → Square (r) (sym q) (r ∙∙ p ∙∙ q) (p)
lemma2 square i j = square (~ j ) i

 