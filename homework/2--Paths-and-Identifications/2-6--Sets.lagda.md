# Homework 2-6: Sets
```
module homework.2--Paths-and-Identifications.2-6--Sets where

open import Cubical.Data.Sigma.Base using (Σ ; _×_)
open import Cubical.Foundations.Function using (_∘_; _$_)
open import homework.1--Type-Theory.1-1--Types-and-Functions hiding (_∘_)
open import homework.1--Type-Theory.1-2--Inductive-Types
open import homework.1--Type-Theory.1-3--Propositions-as-Types hiding (¬_)
open import homework.2--Paths-and-Identifications.2-1--Paths hiding (cong)
open import homework.2--Paths-and-Identifications.2-2--Path-Algebra-and-J
open import homework.Library.Univalence
open import homework.2--Paths-and-Identifications.2-4--Composition-and-Filling
open import homework.2--Paths-and-Identifications.2-5--Propositions
open import homework.Library.EquationalReasoning

private
  variable
    ℓ ℓ' ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
    A B P : Type ℓ
```

## Sets

As we have seen in 2-2, paths in inductive types like `Bool`, `ℕ` and
`ℤ` are equalities between elements. As a corollary, the type of paths
`x ≡ y` between two elements `x` and `y` in these types are
propositions --- specifically, the proposition that `x` equals `y`.

```
isSetBool : (x y : Bool) → isProp (x ≡ y)
isSetBool x y =
  let ≡BoolPath≡ = sym $ isoToPath (≡Iso≡Bool x y)
  in subst isProp ≡BoolPath≡ (isProp-≡Bool x y)

isSetℕ : (x y : ℕ) → isProp (x ≡ y)
isSetℕ x y =
  let ≡ℕPath≡ = sym $ isoToPath (≡Iso≡ℕ x y)
  in subst isProp ≡ℕPath≡ (isProp-≡ℕ x y)
```

We will call a type `A` for which `x ≡ y` is a proposition for any `x`
and `y : A` a *set*, with the idea that a set is a type where
identifying two elements (via paths) is a proposition --- namely, the
proposition that the two elements are equal.

```
isSet : Type ℓ → Type ℓ
isSet A = (x y : A) → isProp (x ≡ y)
```

As we've seen above, `Bool` and `ℕ` are sets. We can show a number of
closure properties of sets as well, similar to those closure
properties we showed for propositions.

The type `⊤` is a one-element set, and the empty type `∅` is a set.
```
isSet⊤ : isSet ⊤
isSet⊤ x y = isContr→isProp $ isContrisContr≡ isContr⊤ x y

isSet∅ : isSet ∅
isSet∅ ()
```

If `A` and `B` are sets, then `A × B` is a set.
```
isSet× : isSet A → isSet B → isSet (A × B)
-- Exercise
fst (isSet× pA pB (a1 , b1) (a2 , b2) h1 h2 i j) = pA a1 a2 (λ i₁ → fst (h1 i₁)) (λ i₂ → fst (h2 i₂)) i j
snd (isSet× pA pB (a1 , b1) (a2 , b2) h1 h2 i j) = pB b1 b2 (λ i₁ → snd (h1 i₁)) (λ i₂ → snd (h2 i₂)) i j
```

If `B` is a set, then for any type `A`, the type `A → B` of functions
into `B` is a set.
```
isSet→ : isSet B → isSet (A → B)
-- Exercise
isSet→ pB f g h1 h2 i j a = pB (f a) (g a) (λ i₁ → h1 i₁ a) (λ i₂ → h2 i₂ a) i j
```


We can also show that any proposition is a set. This may sound a bit
odd, but we can think of any proposition `P` as a set with at most one
element --- it is, after all, a type with at most one element.

Hint: Here is the cube we want to fill.

                        refl
                b - - - - - - - - > b
         p    / ^             q   / ^
            /   |               /   |
          /     | refl        /     |
        a - - - - - - - - > a       |
        ^       |           ^       |                    ^   j
        |       |           |       |                  k | /
        |       |           |       |                    ∙ — >
        |       |           |       |                      i
        |       a - - - - - | - - > a
        |     /             |     /
        |   /               |   /
        | /                 | /
        a - - - - - - - - > a

```
isProp→isSet-faces : isProp A → (a : A) → (b : A) → (p : a ≡ b) (q : a ≡ b) → (i : I) (j : I) → I → Partial (~ i ∨ i ∨ ~ j ∨ j) A
isProp→isSet-faces h a b p q i j k (i = i0) = h a (p j) k
isProp→isSet-faces h a b p q i j k (i = i1) = h a (q j) k
isProp→isSet-faces h a b p q i j k (j = i0) = h a a k
isProp→isSet-faces h a b p q i j k (j = i1) = h a b k

isProp→isSet : isProp A → isSet A
-- Exercise
isProp→isSet h a b p q i j = hcomp (isProp→isSet-faces h a b p q i j) a
```

We can use the fact that propositions are closed under retract to
prove that `Σ[ a ∈ A ] B a` is a set whenever `A` is a set and `B a`
is a set for every `a : A`. But to do so, we need a few useful lemmas
about `Σ`-types.

First, `Σ` is a *functor*:
```
Σ-map : {A' : Type ℓ₂} {B : A → Type ℓ₃} {B' : A' → Type ℓ₄}
       (f : A → A')
     → (g : (a : A) → B a → B' (f a))
     → Σ[ a ∈ A ] B a → Σ[ a' ∈ A' ] B' a'
Σ-map f g (a , b) = (f a , g a b)
```

In particular, if `A` is the same as `A'` and `g a : B a → B' a` are
all isomorphisms, then `Σ-map (idfun A) g` is an isomorphism.
```
Σ-cong-iso-snd : {B : A → Type ℓ₃} {B' : A → Type ℓ₄} →
                 ((x : A) → Iso (B x) (B' x)) → Iso (Σ A B) (Σ A B')
Σ-cong-iso-snd {A = A} {B = B} {B' = B'} isom = iso fun inv rightInv leftInv
  where
    fun : (Σ A B) → (Σ A B')
    fun (x , y) = x , Iso.fun (isom x) y

    inv : (Σ A B') → (Σ A B)
    inv (x , y') = x , Iso.inv (isom x) y'

    rightInv : section fun inv
    rightInv (x , y) = ΣPathP (refl , Iso.rightInv (isom x) y)

    leftInv : retract fun inv
    leftInv (x , y') = ΣPathP (refl , Iso.leftInv (isom x) y')
```

Second, we will need to import a function from the library, which we
will inline (so that it works with our homebrew definition of
Iso). Recall from 2-5 the functions `toPathP` and `fromPathP`:

* `toPathP : transport (λ j → B j) b1 ≡ b2 → PathP B b1 b2`
* `fromPathP : PathP B b1 b2 → transport (λ i → B i) b1 ≡ b2`

We will show that these are an isomorphism. First, we can in fact give
a quite simple path (in `Type`) between the types
`transport (λ j → B j)` and `PathP B b1 b2`:

```
PathP≡Path : ∀ (B : I → Type ℓ) (b1 : B i0) (b2 : B i1) →
             PathP B b1 b2 ≡ Path (B i1) (transport (λ i → B i) b1) b2
PathP≡Path B b1 b2 i =
  PathP (λ j → B (i ∨ j)) (transport-filler (λ j → B j) b1 i) b2
```

This is enough to produce an isomorphism between the two types using
`transport`. But already have two maps `toPathP` and `fromPathP`
between these types, and we want those specific maps to be part of an
isomorphism. Verifying that they are inverse takes a lot more work,
unfortunately.

```
-- This is a version of `cong` that works for dependent functions.
cong : {B : A → Type ℓ'} {x y : A}
       (f : (a : A) → B a)
     → (p : x ≡ y)
     → PathP (λ i → B (p i)) (f x) (f y)
cong f p i = f (p i)

hcomp-unique : ∀ {ℓ} {A : Type ℓ} {φ}
             → (u : I → Partial φ A) → (u0 : A [ φ ↦ u i0 ])
             → (h2 : ∀ i → A [ (φ ∨ ~ i) ↦ (λ { (φ = i1) → u i 1=1; (i = i0) → outS u0}) ])
             → (hcomp u (outS u0) ≡ outS (h2 i1)) [ φ ↦ (λ { (φ = i1) → (λ i → u i1 1=1)}) ]
hcomp-unique {φ = φ} u u0 h2 = inS (λ i → hcomp (λ { k (φ = i1) → u k 1=1
                                                   ; k (i = i1) → outS (h2 k) })
                                                (outS u0))

PathPIsoPath : ∀ (A : I → Type ℓ) (x : A i0) (y : A i1) → Iso (PathP A x y) (transport (λ i → A i) x ≡ y)
PathPIsoPath A x y .Iso.fun = fromPathP
PathPIsoPath A x y .Iso.inv = toPathP
PathPIsoPath A x y .Iso.rightInv q k i =
  hcomp
    (λ j → λ
      { (i = i0) → slide (j ∨ ~ k)
      ; (i = i1) → q j
      ; (k = i0) → transp (λ l → A (i ∨ l)) i (fromPathPFiller j)
      ; (k = i1) → ∧∨Square i j
      })
    (transp (λ l → A (i ∨ ~ k ∨ l)) (i ∨ ~ k)
      (transp (λ l → (A (i ∨ (~ k ∧ l)))) (k ∨ i)
        (transp (λ l → A (i ∧ l)) (~ i)
          x)))
  where
  fromPathPFiller : _
  fromPathPFiller =
    hfill
      (λ j → λ
        { (i = i0) → x
        ; (i = i1) → q j })
      (inS (transp (λ j → A (i ∧ j)) (~ i) x))

  slide : I → _
  slide i = transp (λ l → A (i ∨ l)) i (transp (λ l → A (i ∧ l)) (~ i) x)

  ∧∨Square : I → I → _
  ∧∨Square i j =
    hcomp
      (λ l → λ
        { (i = i0) → slide j
        ; (i = i1) → q (j ∧ l)
        ; (j = i0) → slide i
        ; (j = i1) → q (i ∧ l)
        })
      (slide (i ∨ j))
PathPIsoPath A x y .Iso.leftInv q k i =
  outS
    (hcomp-unique
      (λ j → λ
        { (i = i0) → x
        ; (i = i1) → transp (λ l → A (j ∨ l)) j (q j)
        })
      (inS (transp (λ l → A (i ∧ l)) (~ i) x))
      (λ j → inS (transp (λ l → A (i ∧ (j ∨ l))) (~ i ∨ j) (q (i ∧ j)))))
    k
```

With this isomorphism in hand, we can revisit the path types in `Σ` types.
```
-- We need a few lemmas about isomorphisms: they compose and can be inverted!
compIso : {ℓ'' ℓ''' : _} {B : Type ℓ''} {C : Type ℓ'''}
        → Iso A B → Iso B C → Iso A C
compIso {A = A} {C = C} i j = iso fun inv rightInv leftInv
  where
  fun : A → C
  fun = Iso.fun j ∘ Iso.fun i

  inv : C → A
  inv = Iso.inv i ∘ Iso.inv j

  rightInv : section fun inv
  rightInv b = cong (Iso.fun j) (Iso.rightInv i (Iso.inv j b)) ∙ Iso.rightInv j b

  leftInv : retract fun inv
  leftInv a = cong (Iso.inv i) (Iso.leftInv j (Iso.fun i a)) ∙ Iso.leftInv i a

invIso : Iso A B → Iso B A
invIso f = iso (Iso.inv f) (Iso.fun f) (Iso.leftInv f) (Iso.rightInv f)

ΣPathTransport :{B : A → Type ℓ'} (a b : Σ A B) → Type _
ΣPathTransport {B = B} a b =
  Σ[ p ∈ (fst a ≡ fst b) ] transport (λ i → B (p i)) (snd a) ≡ snd b

ΣPathIsoPathΣ : {A : I → Type ℓ} {B : (i : I) → (a : A i) → Type ℓ'}
                {x : Σ (A i0) (B i0)} {y : Σ (A i1) (B i1)} →
  Iso (Σ[ p ∈ PathP A (fst x) (fst y) ] (PathP (λ i → B i (p i)) (snd x) (snd y)))
                      (PathP (λ i → Σ (A i) (B i)) x y)
Iso.fun ΣPathIsoPathΣ        = ΣPathP
Iso.inv ΣPathIsoPathΣ        = PathPΣ
Iso.rightInv ΣPathIsoPathΣ _ = refl
Iso.leftInv ΣPathIsoPathΣ _  = refl

IsoΣPathTransportPathΣ :
  {A : Type ℓ} {B : A → Type ℓ'}
  (a b : Σ A B) → Iso (ΣPathTransport a b) (a ≡ b)
IsoΣPathTransportPathΣ {B = B} a b =
  compIso (Σ-cong-iso-snd (λ p → invIso (PathPIsoPath (λ i → B (p i)) _ _)))
          ΣPathIsoPathΣ
```

Finally, knowing what isomorphisms are in `Σ` types, we can prove that
`Σ[ a ∈ A ] B a` is a set whenever `A` is a set and `B a` is a set for
any `a : A`.

```
isSetΣ : {B : A → Type ℓ'} → isSet A → ((a : A) → isSet (B a))
       → isSet (Σ A B)
isSetΣ {A = A} {B = B} setA setB x y =
  isPropRetract to fro to-fro isPropΣPathTransport
  where

    isPropΣPathTransport : isProp (ΣPathTransport x y)
    isPropΣPathTransport =
      isPropΣ (setA _ _) λ _ → setB _ _ _

    to : x ≡ y → ΣPathTransport x y
    to =  Σ-map (idfun _) (λ e → fromPathP) ∘ PathPΣ

    fro : ΣPathTransport x y → x ≡ y
    fro = ΣPathP ∘ (Σ-map (idfun _) (λ e → toPathP {B = λ i → B (e i)}))

    to-fro : retract to fro
    to-fro p i = ΣPathP (cong fst p , PathPIsoPath (λ j → B (fst (p j))) (snd x) (snd y) .Iso.leftInv (cong snd p) i)
```

Similar to contractible types and propositions, we have that any
retract of a set is a set.

```
isSetRetract :
  (f : A → B) (g : B → A)
  (h : (x : A) → g (f x) ≡ x)
  → isSet B → isSet A
-- Exercise
-- isSetRetract f g h set x y p q i j =
isSetRetract f g h set x y p q i j =
  hcomp (λ k → λ { (i = i0) → h (p j) k
                 ; (i = i1) → h (q j) k
                 ; (j = i0) → h x k
                 ; (j = i1) → h y k})
        (g (set (f x) (f y)
                (cong f p) (cong f q) i j))
```
## Types which are not sets.

Not all types are sets. In particular, the type of types is not a set.
```
not-Path : Bool ≡ Bool
not-Path = isoToPath not-Iso

¬isSet-Type : ¬ isSet Type
¬isSet-Type s = true≢false (λ i → transport (bad-Path i) true)
  where bad-Path : refl ≡ not-Path
        bad-Path = s Bool Bool refl not-Path
```

We can also define higher inductive types which are not sets. This
type is called the "circle" (written by topologists as $S¹$), since it
contains a point `base` and a path `loop` which goes from `base` to
`base`, forming a circle.

```
data S¹ : Type where
  base : S¹
  loop : base ≡ base
```

To show that `S¹` is not a set, we can define its "double cover" - a
type family with two elements over the base point, but for which
`transport`ing along the `loop` flips those two points. Use this to
show that `S¹` is also not a set.

```
double-cover : S¹ → Type
double-cover base = Bool
double-cover (loop i) = isoToPath not-Iso i

¬isSet-S¹ : ¬ isSet S¹
-- Exercise
¬isSet-S¹ p = true≢false (λ i → subst double-cover (uhoh i) true)
  where uhoh = p base base refl loop
```
