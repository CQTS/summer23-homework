# Homework X: Higher Types
```
module homework-solutions.Extra.Circle where

open import Cubical.Data.Sigma.Base
open import Cubical.Foundations.Prelude using (cong; subst; refl)


open import homework-solutions.1--Type-Theory.1-1--Types-and-Functions
open import homework-solutions.1--Type-Theory.1-2--Inductive-Types
open import homework-solutions.1--Type-Theory.1-3--Propositions-as-Types hiding (¬_)
open import homework-solutions.2--Paths-and-Identifications.2-1--Paths using (true≢false; Iso; iso; not-Iso; sucℤ-Iso)
open import homework-solutions.2--Paths-and-Identifications.2-2--Path-Algebra-and-J
open import homework-solutions.Library.Univalence
open import homework-solutions.2--Paths-and-Identifications.2-4--Composition-and-Filling
open import homework-solutions.2--Paths-and-Identifications.2-5--Propositions
open import homework-solutions.2--Paths-and-Identifications.2-6--Sets hiding (cong)

```

References:
https://1lab.dev/Homotopy.Space.Circle.html

* Higher Inductive Types
  * The circle
  * The torus
  * the torus is the circle squared

* Type families on higher inductive types
  * The double cover of the circle
  * The universal cover of the circle

* Computing the loop space of the circle


FunIsoFunctionalGraph : {A B : Type} → Iso (A → B) (Σ[ R ∈ Rel A B ] (isFunctional R))
FunIsoFunctionalGraph {A} {B} = iso to fro s r
  where
    to : (A → B) → Σ[ R ∈ Rel A B ] (isFunctional R)
    to f = graphRel f , isFunctionalGraph f

    open import Cubical.Foundations.Function
    fro : Σ[ R ∈ Rel A B ] (isFunctional R) → (A → B)
    fro = uncurry isFunctional→Fun

    s : section to fro
    s (R , c) = {!!}

    r : retract to fro
    r f = refl


```
S¹-rec : ∀ {ℓ} {A : Type ℓ} (a : A) (l : a ≡ a)
       → S¹ → A
S¹-rec a l base = a
S¹-rec a l (loop i) = l i

möbius : S¹ → Type
möbius base = Bool
möbius (loop i) = not-Path i

refl≢loop : ¬ refl ≡ loop
refl≢loop path = true≢false λ i → subst möbius (path i) true

loopⁿ : ℤ → base ≡ base
loopⁿ (pos zero) = refl
loopⁿ (pos (suc n)) = loopⁿ (pos n) ∙ loop
loopⁿ (negsuc zero) = sym loop
loopⁿ (negsuc (suc n)) = loopⁿ (negsuc n) ∙ sym loop

bouquet-gen : ∀ {ℓ} {A : Type ℓ} → A → ΩBouquet A
bouquet-gen a = stem a ∙∙ flower a ∙∙ sym (stem a)

to-bouquet : ∀ {ℓ} {A : Type ℓ} (sA : isSet A) → InvList A → ΩBouquet A
to-bouquet sA ε = refl
to-bouquet sA (a :∙: L) = (bouquet-gen a) ∙ (to-bouquet sA L)
to-bouquet sA (a ⁻¹:∙: L) = sym (bouquet-gen a) ∙ to-bouquet sA L
to-bouquet sA (section-law a L i) = {!!}
to-bouquet sA (retract-law a L i) = {!!}
to-bouquet sA (is-set L L₁ x y i i₁) = {!!}
```
             line1
         pt  - - - > pt
          ^           ^
    line2 |           | line2    ^
          |           |        j |
         pt  — — — > pt          ∙ — >
             line1                 i
```
data Torus : Type where
  point : Torus
  line1 : point ≡ point
  line2 : point ≡ point
  square : Square line2 line2 line1 line1
```

```
t2c : Torus → S¹ × S¹
t2c point        = ( base , base )
t2c (line1 i)    = ( loop i , base )
t2c (line2 j)    = ( base , loop j )
t2c (square i j) = ( loop i , loop j )

c2t : S¹ × S¹ → Torus
c2t (base   , base)   = point
c2t (loop i , base)   = line1 i
c2t (base   , loop j) = line2 j
c2t (loop i , loop j) = square i j

c2t-t2c : (t : Torus) → c2t (t2c t) ≡ t
c2t-t2c point        = refl
c2t-t2c (line1 _)    = refl
c2t-t2c (line2 _)    = refl
c2t-t2c (square _ _) = refl

t2c-c2t : (p : S¹ × S¹) → t2c (c2t p) ≡ p
t2c-c2t (base   , base)   = refl
t2c-c2t (base   , loop _) = refl
t2c-c2t (loop _ , base)   = refl
t2c-c2t (loop _ , loop _) = refl
```

```
{-
helix : S¹ → Type₀
helix base     = ℤ
helix (loop i) = sucPathℤ i
-}
```


```
data Susp (A : Type) : Type where
  north : Susp A
  south : Susp A
  merid : (a : A) → north ≡ south
```

Dumb but maybe good starting exercise:
```
data Interval : Type where
  zero : Interval
  one  : Interval
  seg  : zero ≡ one

isContrInterval : isContr Interval
isContrInterval = (zero , contr)
  where
  contr : (x : Interval) → zero ≡ x
  contr zero      = refl
  contr one       = seg
  contr (seg i) j = connection∧ seg i j

SuspUnit≅Interval : Iso (Susp ⊤) Interval
-- Exercise (trivial):
-- SuspUnit≅Interval = {!!}
Iso.fun SuspUnit≅Interval north = zero
Iso.fun SuspUnit≅Interval south = one
Iso.fun SuspUnit≅Interval (merid tt i) = seg i
Iso.inv SuspUnit≅Interval zero = north
Iso.inv SuspUnit≅Interval one = south
Iso.inv SuspUnit≅Interval (seg i) = merid tt i
Iso.rightInv SuspUnit≅Interval zero = refl
Iso.rightInv SuspUnit≅Interval one = refl
Iso.rightInv SuspUnit≅Interval (seg i) = refl
Iso.leftInv SuspUnit≅Interval north = refl
Iso.leftInv SuspUnit≅Interval south = refl
Iso.leftInv SuspUnit≅Interval (merid tt i) = refl
```

```
SuspBool≅S¹ : Iso (Susp Bool) S¹
-- Exercise:
-- SuspBool≅S¹ = {!!}
Iso.fun SuspBool≅S¹ north = base
Iso.fun SuspBool≅S¹ south = base
Iso.fun SuspBool≅S¹ (merid true i) = loop i
Iso.fun SuspBool≅S¹ (merid false i) = base
Iso.inv SuspBool≅S¹ base = north
Iso.inv SuspBool≅S¹ (loop i) = (merid true ∙ sym (merid false)) i
Iso.rightInv SuspBool≅S¹ base = refl
Iso.rightInv SuspBool≅S¹ (loop i) j = sym (rUnit loop) j i
Iso.leftInv SuspBool≅S¹ north = refl
Iso.leftInv SuspBool≅S¹ south = merid false
Iso.leftInv SuspBool≅S¹ (merid true i) j = compPath-filler (merid true) (sym (merid false)) (~ j) i
Iso.leftInv SuspBool≅S¹ (merid false i) j = connection∧ (merid false) i j
```

```
sucℤ-Path : ℤ ≡ ℤ
sucℤ-Path = isoToPath sucℤ-Iso

helix : S¹ → Type
helix base = ℤ
helix (loop i) = sucℤ-Path i

S¹-encode : (x : S¹) → base ≡ x → helix x
S¹-encode _ p = subst helix p (pos zero)

predSuc-Path : (n : ℤ) → predℤ (sucℤ n) ≡ n
-- Exercise: (We proved this in 2-1 as part of showing that `sucℤ` is
-- an `Iso`, so just extract the relevant field from that Iso)
-- predSuc-Path = {!!}
predSuc-Path = Iso.leftInv sucℤ-Iso

S¹-decode : (x : S¹) → helix x → base ≡ x
```

Decode is a bit of a pain. In the `(loop i)` case, we will be asked to
complete the following square: (In the following diagrams, the
vertices are all `base : S¹`.)

                loop
            * - - - - > *
            ^           ^
    loopⁿ y |           | loopⁿ y         ^
            |           |               j |
            * — — — - > *                 ∙ — >
                refl                        i

mvrnote: crappy justification:

It might look odd to have `loopⁿ y j` on both sides. The reason is
that the integer `y` varies as `i` goes from `i0` to `i1`, going from
some `n` to `n+1`. And so the square should commute: going around
either way should be `loopⁿ (suc n) j`. The reason it is not literally
written this way is that `y` is some element of `sucℤ-Path i`, which
some type along the path `sucℤ-Path` in the universe, and not the type
`ℤ`.

We can build this square as an `hcomp`. Here's the cube we are going
to fill, with the desired square sitting on the top.

                                      loop
                                * - - - - - - - - > *
                    loopⁿ y   / ^                 / ^
                            /   |               / loopⁿ y
                          /     | refl        /     |
                        * - - - - - - - - > *       |
                        ^       |           ^       |                    ^   j
                        |       |           |       |                  k | /
                        |       |           |       |                    ∙ — >
                        |       |    loop   |       |                      i
                        |       * - - - - - | - - > *
    loopⁿ (predℤ (suzℤ y))    /             |     /
                        |   /               |   /  loopⁿ y
                        | /                 | /
                        * - - - - - - - - > *
                                refl

Three of the sides are easy, just constant in one of the dimensions.
```
S¹-decode-faces : (i : I) → (y : sucℤ-Path i) → (j : I) → I → Partial (i ∨ ~ i ∨ j ∨ ~ j) S¹

S¹-decode-faces i y j k (i = i1) = loopⁿ y j
S¹-decode-faces i y j k (j = i0) = base
S¹-decode-faces i y j k (j = i1) = loop i
```

The `(i = i0)` face is more slightly more interesting, here it is written flat:

                loopⁿ y
            * - - - - - > *
            ^             ^
       refl |             | refl              ^
            |             |                 k |
            * — — — - - > *                   ∙ — >
         loopⁿ (predℤ (suzℤ y))                 j

For this we can combine `loopⁿ` with `predSuc-Path` in the first argument.
```
S¹-decode-faces i y j k (i = i0) = loopⁿ (predSuc-Path y k) j
```

All that remains is to construct the base square, and for this we have
to get our hands dirty. For every `n`, we need a square

                        loop
                    * - - - - > *
                    ^           ^
    loopⁿ (predℤ n) |           | loopⁿ n           ^
                    |           |                 j |
                    * — — — - > *                   ∙ — >
                        refl                          i

Constructing these squares will need to make reference to our actual
defintion of `predℤ`, so we split into the same three cases as were
used for `predℤ`: `pos zero`, `pos (suc n)` and `negsuc n`.

```
S¹-decode-base : (n : ℤ) → Square (loopⁿ (predℤ n)) (loopⁿ n) refl loop

```

The simplest case is `pos zero`:

                   loop
               * - - - - > *
               ^           ^
     sym loop  |           | refl              ^
               |           |                 j |
               * — — — - > *                   ∙ — >
                   refl                          i

and this is easy to build using a connection.

```
S¹-decode-base (pos zero) i j = loop (i ∨ ~ j)
```

Next we have `pos (suc n)`, which is exactly one of the composition
fillers we've seen already.

                        loop
                    * - - - - > *
                    ^           ^
    loopⁿ (pos n) j |           | loopⁿ (pos n) ∙ loop          ^
                    |           |                             j |
                    * — — — - > *                               ∙ — >
                        refl                                      i

```
S¹-decode-base (pos (suc n)) i j = compPath-filler (loopⁿ (pos n)) loop i j
```

And the final case for `negsuc n` is similar.

                                    loop
                                * - - - - > *
                                ^           ^
    loopⁿ (negsuc n) ∙ sym loop |           | loopⁿ (negsuc n)              ^
                                |           |                             j |
                                * — — — - > *                               ∙ — >
                                    refl                                      i

This is actually also an instance of `compPath-filler`, but we have to
flip the direction of `i` because the composition is now happening at
`i = i0`.

```
S¹-decode-base (negsuc n) i j = compPath-filler (loopⁿ (negsuc n)) (sym loop) (~ i) j
```

Finally, we perform the actual `hcomp`.
```
S¹-decode base = loopⁿ
S¹-decode (loop i) y j =
  hcomp (S¹-decode-faces i y j)
        (S¹-decode-base (unglue (i ∨ ~ i) y) i j)
```

Checking that one composite is equal to the identity is easy using J,
because everything computes away when the input path `p` is `refl`:
```
S¹-decodeEncode : (p : base ≡ base) → S¹-decode base (S¹-encode base p) ≡ p
S¹-decodeEncode p = J (λ y q → S¹-decode y (S¹-encode y q) ≡ q) (λ _ → refl) p
```

And the other way can be verified by induction on `ℤ`. (Remember that
`decode base` is just `loopⁿ`, so we don't have to worry about the
complicated `hcomp`.)

```
S¹-encodeDecode : (n : ℤ) → S¹-encode base (S¹-decode base n) ≡ n
S¹-encodeDecode (pos zero) = refl
S¹-encodeDecode (pos (suc n)) = cong sucℤ (S¹-encodeDecode (pos n))
S¹-encodeDecode (negsuc zero) = refl
S¹-encodeDecode (negsuc (suc n)) = cong predℤ (S¹-encodeDecode (negsuc n))
```

And we're done!
```
ΩS¹Isoℤ : Iso (base ≡ base) ℤ
Iso.fun ΩS¹Isoℤ      = S¹-encode base
Iso.inv ΩS¹Isoℤ      = S¹-decode base
Iso.rightInv ΩS¹Isoℤ = S¹-encodeDecode
Iso.leftInv ΩS¹Isoℤ  = S¹-decodeEncode
```

# Bonus: Paths in higher loops commute

```
EH-base : ∀ {ℓ} {A : Type ℓ} {x : A} → (α β : refl {x = x} ≡ refl)
         → (λ i → α i ∙ refl) ∙ (λ i → refl ∙ β i)
          ≡ (λ i → refl ∙ β i) ∙ (λ i → α i ∙ refl)
EH-base α β i = (λ j → α (~ i ∧ j) ∙ β (i ∧ j)) ∙ λ j → α (~ i ∨ j) ∙ β (i ∨ j)

EH : ∀ {ℓ} {A : Type ℓ} {x : A} → (α β : refl {x = x} ≡ refl) → α ∙ β ≡ β ∙ α
EH {A = A} α β i j z =
  hcomp (λ k → λ { (i = i0) → ((cong (λ x → rUnit x (~ k)) α) ∙ (cong (λ x → lUnit x (~ k)) β)) j
                 ; (i = i1) → ((cong (λ x → lUnit x (~ k)) β) ∙ (cong (λ x → rUnit x (~ k)) α)) j
                 ; (j = i0) → rUnit refl (~ k)
                 ; (j = i1) → rUnit refl (~ k)})
  (EH-base α β i j) z
```
