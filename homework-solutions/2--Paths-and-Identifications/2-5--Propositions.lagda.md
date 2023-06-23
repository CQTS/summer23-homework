# Homework 2-5: Propositions
```
module homework-solutions.2--Paths-and-Identifications.2-5--Propositions where

open import Cubical.Data.Sigma.Base using (Σ ; _×_)
open import Cubical.Foundations.Prelude using (cong)
open import Cubical.Foundations.Function using (_∘_)

open import homework-solutions.1--Type-Theory.1-1--Types-and-Functions hiding (_∘_)
open import homework-solutions.1--Type-Theory.1-2--Inductive-Types
open import homework-solutions.1--Type-Theory.1-3--Propositions-as-Types hiding (¬_)
open import homework-solutions.2--Paths-and-Identifications.2-1--Paths hiding (cong)
open import homework-solutions.2--Paths-and-Identifications.2-2--Path-Algebra-and-J
open import homework-solutions.Library.Univalence
open import homework-solutions.2--Paths-and-Identifications.2-4--Composition-and-Filling
open import homework-solutions.Library.EquationalReasoning

private
  variable
    ℓ ℓ' : Level
    A B P : Type ℓ
```

Topics covered:
* Equational reasoning syntax
* Propositions
  * Closure properties
* Propositional truncation
  * Definition as a higher inductive type
  * `∨` and `∃` as propositional truncations
* Decidable types
* Subtypes

## Aside: Equational Reasoning

In the upcoming sections, we will often produce a desired path by
chaining together several simpler ones. The cubical library provides
some nice syntax which keeps track of the endpoints of all the paths.

For example:
```
private
  example1 : (w x y z : A) (p : w ≡ x) (q : x ≡ y) (r : y ≡ z) → w ≡ z
  example1 w x y z p q r =
    w ≡⟨ p ⟩
    x ≡⟨ q ⟩
    y ≡⟨ r ⟩
    z ∎

  example2 : (f : A → B) (g : B → A)
           → (η : (x : A) → x ≡ g (f x))
           → (ε : (y : B) → f (g y) ≡ y)
           → (x : A) → f x ≡ f x
  example2 f g η ε x =
    f x         ≡⟨ cong f (η x) ⟩
    f (g (f x)) ≡⟨ ε (f x) ⟩
    f x         ∎
```

We encourage you to use this syntax when chaining paths together, it
makes it a lot easier to see what's going on!

## Propositions

In Lecture 1-3, we saw how types could represent propositions. But not
all types represent propositions. Some, like `Bool` and `ℕ`, are data
types which do not represent any proposition. What makes a type a
proposition, then?

Recall that when thinking of a type `A` as a proposition, an element
`a : A` is (a witness to) the fact that `A` is true. For propositions
`A`, we only care about whether `A` has an element at all, whereas for
data types, it matters which particular element we have. We turn this
observation into a definition: propositions are types which have at
most one element. In other words, a type is a proposition when we can
give a path between any two elements.

```
isProp : Type ℓ → Type ℓ
isProp A = (x y : A) → x ≡ y
```

If a type has no elements at all then it certainly has at most one
element, so we should expect `∅` to be a proposition. As we saw in
Lecture 1-3, `∅` represents the proposition with no proof --- false.

```
isProp∅ : isProp ∅
isProp∅ ()
```

As we saw in Lecture 2-3, contractible types may be thought of as
types with a unique element. Of course, a type with just one element
has at most one element, so we should expect contractible types to be
propositions.

```
isContr→isProp : isContr A → isProp A
isContr→isProp (x , p) a b =
  a ≡⟨ sym (p a) ⟩
  x ≡⟨ p b ⟩
  b ∎
```

The type `⊤` is contractible and represents a proposition with a given
proof `tt : ⊤` --- truth.

```
isProp⊤ : isProp ⊤
isProp⊤ = isContr→isProp isContr⊤
```

Using this, we can show that the equality relations defined in 1-3 are
propositions.

```
isProp-≡Bool : (a b : Bool) → isProp (a ≡Bool b)
isProp-≡Bool true true = isProp⊤
isProp-≡Bool true false = isProp∅
isProp-≡Bool false true = isProp∅
isProp-≡Bool false false = isProp⊤

isProp-≡ℕ : (n m : ℕ) → isProp (n ≡ℕ m)
-- Exercise
--isProp-≡ℕ n m = ?
isProp-≡ℕ zero zero = isProp⊤
isProp-≡ℕ zero (suc m) = isProp∅
isProp-≡ℕ (suc n) zero = isProp∅
isProp-≡ℕ (suc n) (suc m) = isProp-≡ℕ n m
```

The ordering on the natural numbers is also a proposition.
```
isProp-≤ℕ : (n m : ℕ) → isProp (n ≤ℕ m)
isProp-≤ℕ zero m = isProp⊤
isProp-≤ℕ (suc n) zero = isProp∅
isProp-≤ℕ (suc n) (suc m) = isProp-≤ℕ n m
```

On the other hand, if a type has at most one element and also has an
element, then that element is unique. In other words, if a proposition
has an element, then it is contractible.

```
Prop-with-point-isContr : isProp A → A → isContr A
-- Exercise:
-- Prop-with-point-isContr p a = {!!}
Prop-with-point-isContr p a = a , p a
```

We can go the other way too. If, whenever `A` has an element, it has a
unique element, then it has at most one element.

```
isContr-prop-with-point : (A → isContr A) → isProp A
-- Exercise:
-- isContr-prop-with-point c x y = ?
isContr-prop-with-point c x y =
  x         ≡⟨ sym (snd (c x) x) ⟩
  fst (c x) ≡⟨ (snd (c x) y) ⟩
  y         ∎
```

More interestingly, we can show that being contractible is a
proposition. That is, `isContr A` is a proposition for any type `A`:
the proposition that `A` has a unique element.

The proof is a bit tricky. Suppose we have two elements `(c0, h0)` and
`(c1, h1)` of `isContr A`, seeking to give a path `(c0, h0) ≡ (c1, h1)`.
As these are pairs, it suffices to give two paths, one in the first
component and the other in the second component lying over the first.

```
isPropIsContr : isProp (isContr A)
fst (isPropIsContr (c0 , h0) (c1 , h1) j) = h0 c1 j
```

For the first component, we can use one of the witnesses of
contractibility to get `h0 c1 : c0 ≡ c1`. For the second, then, we
need to construct a path over this showing that for any `y : A` we
have "`h0 y ≡ h1 y1` over `h0 c1'", which is the square on the top of
the following cube:

                       h1 y
               c1 - - - - - - - - > y
              / ^                 / ^
     h0 c1  /   |               /   |
          /     | h0 y        /  y  |
       c0 - - - - - - - - > y       |
        ^       |           ^       | h0 y               ^   j
        |       |           |       |                  k | /
        |       |           |       |                    ∙ — >
        |       |           |       |                      i
        |      c0 - - - - - | - - > c0
        |     /             |     /
        |   /               |   /
        | /                 | /
       c0 - - - - - - - - > c0


To fill this square, we will use an `hcomp` on the open box above. The
bottom of this box will be constant at c0, while the sides will be
filled in using `h0` and `h1`.
```
snd (isPropIsContr (c0 , h0) (c1 , h1) j) y i =
   hcomp {φ = ∂ i ∨ ∂ j} (λ k →
     λ { (i = i0) → h0 (h0 c1 j) k;  -- We could do h0 c1 (j ∧ k)
         (i = i1) → h0 y k;
         (j = i0) → h0 (h0 y i) k;   -- and h0 y (i ∧ k)
         (j = i1) → h0 (h1 y i) k})
     c0
```

We can also show that `isProp A` is itself a proposition, using
another cube. The main fact is that, in a proposition, you can fill
any square that you want, regardless of what the sides are. We state
this in full generality, because we are going to use it later.

```
SquareP :
  (A : I → I → Type ℓ)
  {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} (a₀₋ : PathP (λ j → A i0 j) a₀₀ a₀₁)
  {a₁₀ : A i1 i0} {a₁₁ : A i1 i1} (a₁₋ : PathP (λ j → A i1 j) a₁₀ a₁₁)
  (a₋₀ : PathP (λ i → A i i0) a₀₀ a₁₀) (a₋₁ : PathP (λ i → A i i1) a₀₁ a₁₁)
  → Type ℓ
SquareP A a₀₋ a₁₋ a₋₀ a₋₁ = PathP (λ i → PathP (λ j → A i j) (a₋₀ i) (a₋₁ i)) a₀₋ a₁₋

isProp→SquareP : ∀ {A : I → I → Type ℓ} → ((i j : I) → isProp (A i j))
             → {a : A i0 i0} {b : A i0 i1} {c : A i1 i0} {d : A i1 i1}
             → (r : PathP (λ j → A j i0) a c) (s : PathP (λ j → A j i1) b d)
             → (t : PathP (λ j → A i0 j) a b) (u : PathP (λ j → A i1 j) c d)
             → SquareP A t u r s
isProp→SquareP {A = A} isPropB {a = a} r s t u i j =
  hcomp (λ { k (i = i0) → isPropB i0 j (base i0 j) (t j) k
           ; k (i = i1) → isPropB i1 j (base i1 j) (u j) k
           ; k (j = i0) → isPropB i i0 (base i i0) (r i) k
           ; k (j = i1) → isPropB i i1 (base i i1) (s i) k
        }) (base i j) where
    base : (i j : I) → A i j
    base i j = transport (λ k → A (i ∧ k) (j ∧ k)) a

isPropIsProp : isProp (isProp A)
isPropIsProp isProp1 isProp2 i a b = isProp→SquareP (λ _ _ → isProp1) refl refl (isProp1 a b) (isProp2 a b) i
```

## Closure Properties of Propositions

Propositions are closed under our usual type operations. When we use
the ordinary type formers on propositions, the result is often the
logical version of that operation. For example if `B : A → Type` is a
family of propositions depending on `A`, then the type of functions
`(a : A) → B a` is a proposition; specifically, this is the
proposition that for all `a : A`, the proposition `B a` holds.

```
isPropFun : {A : Type ℓ} {B : A → Type ℓ'}
            (p : ∀ a → isProp (B a))
          → isProp (∀ a → B a)
-- Exercise
-- isPropFun p f g = ?
isPropFun p f g i a = p a (f a) (g a) i
```

As a special case of "for all", we get "implies". If `A` and `B` are
propositions, then the type of functions `A → B` is a proposition ---
namely, the proposition that `A` implies `B`.

```
isProp→ : isProp B → isProp (A → B)
isProp→ p = isPropFun (λ _ → p)
```

If `B` is true, then `A → B` is also true. If contractible types
correspond to true propositions, we should have that `A → B` is
contractible whenever `B` is contractible.

```
isContr→ : isContr B → isContr (A → B)
fst (isContr→ (cB , hB)) = λ _ → cB
snd (isContr→ (cB , hB)) f i a = hB (f a) i
```

If two propositions imply each other, then they are in fact
isomorphic. This is known as "proposition extensionality".

```
propExt : isProp A → isProp B
        → (A → B) → (B → A)
        → Iso A B
-- Exercise
-- Iso.fun (propExt isPropA isPropB f g) = f
-- Iso.inv (propExt isPropA isPropB f g) = g
-- Iso.rightInv (propExt isPropA isPropB f g) b = isPropB (f (g b)) b
-- Iso.leftInv (propExt isPropA isPropB f g) a = isPropA (g (f a)) a
Iso.fun (propExt isPropA isPropB f g) = f
Iso.inv (propExt isPropA isPropB f g) = g
Iso.rightInv (propExt isPropA isPropB f g) b = isPropB (f (g b)) b
Iso.leftInv (propExt isPropA isPropB f g) a = isPropA (g (f a)) a
```

We could in fact show that `A iffP B` is isomorphic to `Iso A B`.

As a special case of implication, we find that type negation `¬`
always yields a proposition, since we defined `¬ A = A → ∅`.

```
-- We redefine ¬ here because we want it to be valid for all universe
-- levels `ℓ`.
infix 3 ¬_
¬_ : Type ℓ → Type ℓ
¬ A = A → ∅

isProp¬ : isProp (¬ A)
isProp¬ = isProp→ isProp∅
```

The "and" of two proposition `A` and `B` is the type of pairs `A × B`.
```
isProp× : isProp A → isProp B → isProp (A × B)
isProp× pA pB (a1 , b1) (a2 , b2) i = (pA a1 a2 i) , (pB b1 b2 i)
```

Similarly to `→`, if `A` and `B` are true (contracible), then `A × B` should
also be contractible.
```
isContr× : isContr A → isContr B → isContr (A × B)
fst (isContr× (cA , hA) (cB , hB)) = cA , cB
snd (isContr× (cA , hA) (cB , hB)) (a , b) i = (hA a i) , (hB b i)
```

One last useful closure condition: if `A` is a retract of `B`, then in
some sense `A` is a continuous shrinking of `B`. And so if `B` is a
proposition, then `A` must be too:

```
isPropRetract :
  (f : A → B) (g : B → A)
  → (h : retract f g)
  → isProp B → isProp A
-- Exercise
-- isPropRetract f g h isPropB x y i =
isPropRetract f g h isPropB x y i =
  hcomp
    (λ j → λ
      { (i = i0) → h x j
      ; (i = i1) → h y j})
    (g (isPropB (f x) (f y) i))
```

And similarly for contractible types:
```
isContrRetract :
    (f : A → B) (g : B → A)
  → (h : retract f g)
  → isContr B → isContr A
-- Exercise
-- fst (isContrRetract f g h (center , contr)) = ?
-- snd (isContrRetract f g h (center , contr)) x = ?
fst (isContrRetract f g h (center , contr)) = g center
snd (isContrRetract f g h (center , contr)) x =
  g center ≡⟨ cong g (contr (f x)) ⟩
  g (f x)  ≡⟨ h x ⟩
  x ∎
```

## Propositional Truncation

We are missing two important logical operations: "there exists" and
"or". For these, we will need another construction: the *propositional
truncation* which takes any type `A` and forms a proposition `∃ A` ---
the proposition that "there exists some element of A". An element of
`∃ A` will be a proof that `A` has some element, though it won't be
any particular element of `A`.

We define `∃ A` as a (higher) inductive type with two
constructors.

```
infix 3 ∃_
data ∃_ (A : Type ℓ) : Type ℓ where
  ∣_∣ : A → ∃ A
  squash : (x y : ∃ A) → x ≡ y
```

The first, written `|_| : A → ∃ A`, says that to prove that there
exists an element in `A`, it suffices to give an actual element of
`A`.  The second constructor forces `∃ A` to be a proposition. This is
a recursive constructor (like `suc` is for `ℕ`).

That second constructor is exactly what is needed to prove `isProp (∃ A)`.
```
isProp-∃ : isProp (∃ A)
isProp-∃ = squash
```

The usual terminology for propositional truncation in homotopy type
theory and in the cubical library is `∥ A ∥`, though this can get
confusing if we are doing quantum mechanics where the same bars denote
the norm of a vector or operator. We'll record it here anyway.

```
∥_∥ : Type ℓ → Type ℓ
∥ A ∥ = ∃ A
```

The recursion principle for `∃ A` says that to prove that `∃ A`
implies some proposition `P`, it suffices to assume we have an actual
element `a : A` and then prove `P`. That is, given a function `A → P`,
we can get a function (implication) `∃ A → P`, whenever `P` is a
proposition.

```
∃-rec : (isProp P)
      → (A → P)
      → (∃ A → P)
∃-rec Pprop f ∣ x ∣ = f x
∃-rec Pprop f (squash x y i) = Pprop (∃-rec Pprop f x) (∃-rec Pprop f y) i
```

`∃` should be a "functor", that is, we should be able to go from
functions between types to functions between their truncations. If we have a function from `A` to `B`, then if `A` has an element, `B` also has an element.

```
∃-map : (A → B) → (∃ A → ∃ B)
-- Exercise
-- ∃-map f = ?
∃-map f = ∃-rec isProp-∃ (∣_∣ ∘ f)
```

When `P` is already a proposition, truncating it should do nothing:

```
isProp→equiv∃ : isProp P → Iso P (∃ P)
isProp→equiv∃ isPropP = propExt isPropP isProp-∃ (λ x → ∣ x ∣) (∃-rec isPropP (idfun _))
```

If `P : A → Type` is a family of propositions on `A` --- that is, a
proposition concerning elements of `A` --- then we often like to write
something like "$∃ a : A , P a$" to say that there is an `a : A` such
that `P a` is true. Type theoretically, this is saying that there is
some pair `(a , p)` where `a : A` and `p : P a`. For this reason, we
can define a special syntax that resembles the usual mathematical
notation for existential quantification.

```
∃-syntax : (A : Type ℓ) (B : A → Type ℓ') → Type (ℓ-max ℓ ℓ')
∃-syntax A B = ∃ (Σ A B)

syntax ∃-syntax A (λ x → B) = ∃[ x ∈ A ] B
```

With propositional truncation, we can finally define the proposition
that represents "or" which eluded us in 1-3. There, we thought that
"or" might be represented by `A ⊎ B`, but this is not generally a
proposition even when `A` and `B` are.

```
¬isProp⊤⊎⊤ : ¬ isProp (⊤ ⊎ ⊤)
¬isProp⊤⊎⊤ p =
  let uhoh = p (inl tt) (inr tt)
  in  subst is-inl uhoh tt
  where
      is-inl : ⊤ ⊎ ⊤ → Type
      is-inl (inl _) = ⊤
      is-inl (inr _) = ∅
```

However, it is true that `A ⊎ B` has some element if and only if `A`
has some element or `B` has some element (or both have
elements). Therefore, we can define `A orP B` as the proposition that
there exists an element in `A ⊎ B`.

```
_orP_ : Type ℓ → Type ℓ' → Type _
A orP B = ∃ (A ⊎ B)
```

Challenge:
∃-Idem-×-L-Iso : Iso (∃ (∃ A) × B) (∃ A × B)
∃-Idem-×-L-Iso = {!!}

∃-Idem-×-R-Iso : Iso (∃ A × (∃ B)) (∃ A × B)
∃-Idem-×-R-Iso = {!!}

∃-×-Iso : Iso ((∃ A) × (∃ B)) (∃ A × B)
∃-×-Iso = {!!}

## Decidable Types

If we have a generic proposition `P` we are not allowed to split into
cases for whether `P` is true or false: this would be saying that we
always have an element of `P ⊎ ¬ P` telling us whether `P` holds or
not.

For some types, we do in fact have `P ⊎ ¬ P`; we call such types
"decidable".  The folllowing type is equivalent to `P ⊎ ¬ P`, but with
more meaningful constructor names.

```
data Dec (P : Type ℓ) : Type ℓ where
  yes : ( p :   P) → Dec P
  no  : (¬p : ¬ P) → Dec P
```

Here are the simplest examples:
```
Dec⊤ : Dec ⊤
Dec⊤ = yes tt

Dec∅ : Dec ∅
Dec∅ = no (λ x → x)

DecPt : A → Dec A
DecPt a = yes a
```

Admittedly, decidable types will not be so important for us in the
future, but they are an excellent font of exercises involving
propositions and truncations:

```
¬¬-Stable : Type ℓ → Type ℓ
¬¬-Stable A = ¬ ¬ A → A

Dec→Stable : {A : Type ℓ} → Dec A → ¬¬-Stable A
-- Exercise (fun):
-- Dec→Stable d = {!!}
Dec→Stable (yes x) = λ _ → x
Dec→Stable (no x) = λ f → ∅-rec (f x)

Dec-Idem : Dec (Dec A) → Dec A
Dec-Idem (yes (yes p)) = yes p
Dec-Idem (yes (no ¬p)) = no ¬p
Dec-Idem (no ¬p) = no λ x → ¬p (yes x)

isProp-Dec : isProp A → isProp (Dec A)
isProp-Dec isPropA (yes p₁) (yes p₂) = cong yes (isPropA p₁ p₂)
isProp-Dec isPropA (yes p) (no ¬p) = ∅-rec (¬p p)
isProp-Dec isPropA (no ¬p) (yes p) = ∅-rec (¬p p)
isProp-Dec isPropA (no ¬p₁) (no ¬p₂) = cong no (isProp¬ ¬p₁ ¬p₂)

∃-Dec-Iso : Iso (Dec (∃ A)) (∃ (Dec A))
∃-Dec-Iso = propExt (isProp-Dec isProp-∃) isProp-∃ to fro
  where
    to : Dec (∃ A) → ∃ (Dec A)
    to (yes p) = ∃-map yes p
    to (no ¬p) = ∣ no (λ x → ¬p ∣ x ∣) ∣

    fro-lemma : Dec A → Dec (∃ A)
    fro-lemma (yes p) = yes ∣ p ∣
    fro-lemma (no ¬p) = no (∃-rec isProp∅ ¬p)

    fro : ∃ (Dec A) → Dec (∃ A)
    fro = ∃-rec (isProp-Dec isProp-∃) fro-lemma

¬¬-∃-Iso : Iso (¬ ¬ ∃ A) (¬ ¬ A)
¬¬-∃-Iso = propExt isProp¬ isProp¬ to fro
  where
    to : ¬ ¬ ∃ A → ¬ ¬ A
    to ¬¬∃a ¬a = ¬¬∃a (∃-rec isProp∅ ¬a)

    fro : ¬ ¬ A → ¬ ¬ ∃ A
    fro ¬¬a ¬∃a = ¬¬a (λ x → ¬∃a ∣ x ∣)

Dec→SplitSupport : Dec A → (∃ A → A)
Dec→SplitSupport (yes p) e = p
Dec→SplitSupport (no ¬p) e = ∅-rec (∃-rec isProp∅ ¬p e)
```

## Subtypes

With this definition of proposition, we can define a good notion of
"subtype". If `B : A → Type` is a family of propositions on a type
`A`, then the subtype of `A` carved out by `B` will be the type of
pairs `Σ[ a ∈ A ] B a` whose elements are pairs `(a , b)` where
`a : A` and `b : B a` is a witness that `B` is true of `a`.

The main lemma to prove about subtypes is that they have the same
paths as the types they came from. That is, `(a1 , b1) ≡ (a2 , b2)` is
equivalent to `a1 ≡ a2` whenever `B a` is always a proposition.  To
foreshadow a little, this is extremely useful when we start looking at
algebraic structures such as groups, rings, etc. These come with some
data, together with a bunch of axioms, like associativity,
commutativity, and so on. The lemma we prove tells us that to build a
path between two groups, it's enough to build a path just between the
underlying data, ignoring all the axioms.

We will need an equivalent notion of "proposition depending on `a :
A`", which we've called a "predicate" on `A`.

```
isPred : {A : Type ℓ} (B : A → Type ℓ')
        → Type (ℓ-max ℓ ℓ')
isPred {A = A} B =
    (a1 a2 : A) (p : a1 ≡ a2) (b1 : B a1) (b2 : B a2)
  → PathP (λ i → B (p i)) b1 b2
```

A predicate is a type family `B : A → Type` where for any path `p : a1
≡ a2` we can give a path over `p` from `b1 : B a1` to `b2 : B
a2`. This is an equivalent notion to a family of propositions, which
we can show with a little work.

First, we can show that any predicate is a family of propositions.

```
isPred→∀isProp : {A : Type ℓ} {B : A → Type ℓ'}
               → isPred B → ∀ a → isProp (B a)
isPred→∀isProp p a b1 b2 = p a a refl b1 b2
```

Now the main lemma.

```
Σ≡PropIso : {A : Type ℓ} {B : A → Type ℓ'}
            (p : isPred B)
            (x y : Σ A B)
          → Iso (fst x ≡ fst y) (x ≡ y)
Σ≡PropIso {A = A} {B = B} p x y = iso to (cong fst) to-fro fro-to
  where
    to : fst x ≡ fst y → x ≡ y
    to e = ΣPathP (e , p (fst x) (fst y) e (snd x) (snd y))

    to-fro : section to (cong fst)
    to-fro e i = ΣPathP (cong fst e , to-fro-snd i)
      where
        to-fro-snd : SquareP (λ i j → B (fst (e j))) (p (fst x) (fst y) (cong fst e) (snd x) (snd y)) (λ j → snd (e j)) refl refl
        to-fro-snd = isProp→SquareP (λ i j → isPred→∀isProp p (fst (e j))) _ _ _ _

    fro-to : retract to (cong fst)
    fro-to e i j = e j
```

It will also be useful have an inverse to `isPred→∀isProp`. To go the
other way, we need a few useful library functions which convert
paths-over-paths (in `PathP`) to paths starting at a transport. This
will give us a good opportunity to revisit `transp`.

Recall that `transp` is a built-in function with type:

    transp : ∀ (φ : I) (A : (i : I) → Type) (a : A i0) → A i1

and we used it to define

    transport : {A B : Type ℓ} → A ≡ B → A → B
    transport p a = transp (λ i → p i) i0 a

When transported along `p`, the element `a : A` becomes the element
`transport p a : B`. It seems reasonable for there to be a `PathP`
over the path `p` connecting `a` and `transport p a`:
```
transport-filler : (p : A ≡ B) (x : A)
                   → PathP (λ i → p i) x (transport p x)
```
To get this path, we will use the extra input to `transp` that we have
so far always set to `i0` as in the definition of `transport`.

```
transport-filler p x i = transp (λ j → p (i ∧ j)) (~ i) x
```

The `transp` operation takes in three arguments, `transp p φ x`, where
`p : I → Type ℓ` is a path in types, `φ : I` is a *formula*, and `x :
p i0` is a point in the type at the start of the path `p`. As usual,
to understand how `φ` works, we need to imagine that we are in the
context of some other cubical variables - in the definition of
`transport-filler` we have `i : I` in the context when we use
`transp`. The formula `φ` expresses *where the transport is constant*.
So `transport p x = transp (λ i → p i) i0 x` is not constant anywhere,
but `transport (λ _ → A) i1 x` is constant everywhere and so always
definitionally equals `x`.

In `transport-filler`, the transport is constant when `i = i0`, in
which case we can see that `(λ j → p (i0 ∧ j)) = (λ j → p i0)` is also
constant, and so we have that `transport-filler p x i0 = x`. When
`i = i1`, we have `~ i = i0` and `p (i1 ∧ j) = p j` so that
`transport-filler p x i1 = transp (λ j → p j) i0 x`, which is exactly
the definition of `transport p x`.

Now, returning to converting between `PathP` and paths involving
`transport`.  For the first conversion, `toPathP`, we need to do an
`hcomp` where the base is actually itself a `PathP`.
```
module _ {B : I → Type ℓ} {b1 : B i0} {b2 : B i1} where
  toPathP : transport (λ j → B j) b1 ≡ b2 → PathP B b1 b2
  {-

       b1 ∙ ∙ ∙ ∙ ∙ ∙ ∙ ∙ >  b2
        ^                    ^
     b1 |                    | p                    ^
        |                    |                    j |
       b1 — — — > transport (λ j → B j) b1          ∙ — >
                                                      i
                B i
      B i0 — — — — — — — > B i1
  -}
  toPathP p i = hcomp (λ j → λ { (i = i0) → b1
                               ; (i = i1) → p j })
                      (transport-filler (λ j → B j) b1 i)
```

To go back the other way, we will use `transp` again, but this time in
a different way. Now, when `i = i0` we want `fromPathP p i0 =
transport (λ i → B i) b1` and when `i = i1` we want `fromPathP p i1` =
b2`. So we will ask for `transp` to be constant when `i = i1`.

```
  fromPathP : PathP B b1 b2 → transport (λ i → B i) b1 ≡ b2
  fromPathP p i = transp (λ j → B (i ∨ j)) i (p i)
```

With these functions in hand, we can turn a family of propositions
into a predicate.

```
∀isProp→isPred : {A : Type ℓ} {B : A → Type ℓ'}
               → (∀ a → isProp (B a)) → isPred B
∀isProp→isPred {B = B} p a1 a2 a12 b1 b2 =
  let a12*b1 = (transport (λ i → B (a12 i)) b1)
  in  toPathP (p a2 a12*b1 b2)
```

This lets us easily prove an upgraded, dependent version of `isProp×`.
If `A` is a proposition and `B : A → Type` is a family of propositions
depending on `a : A` (we could think of `B` as a hypothetical
proposition, which only actually exists if `A` is true, as witnessed
by some element `a : A`), then the type of pairs `Σ[ a ∈ A ] B a` is
also a proposition. Really, `Σ A B` represents "`A` and `B`" - but the
proposition `B` only makes sense if `A` is already true.

```
isPropΣ : {A : Type ℓ} {B : A → Type ℓ'}
          (q : isProp A) (p : ∀ a → isProp (B a))
        → isProp (Σ[ a ∈ A ] B a)
isPropΣ q p (a1 , b1) (a2 , b2) i =
  q a1 a2 i , ∀isProp→isPred p a1 a2 (q a1 a2) b1 b2 i
```
