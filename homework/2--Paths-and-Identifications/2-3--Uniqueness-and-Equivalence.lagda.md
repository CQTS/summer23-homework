# Homework 2-3: Uniqueness and Equivalence
```
module homework.2--Paths-and-Identifications.2-3--Uniqueness-and-Equivalence where

open import Cubical.Core.Primitives

open import Cubical.Foundations.Function using (idfun; _∘_; const)
open import Cubical.Data.Sigma.Base using (_×_)

open import homework.1--Type-Theory.1-2--Inductive-Types
open import homework.2--Paths-and-Identifications.2-1--Paths
open import homework.2--Paths-and-Identifications.2-2--Path-Algebra-and-J

private
  variable
    ℓ ℓ' ℓ'' : Level
    A B : Type ℓ
```

* Singletons and contractibility;
  * Definition
  * Singletons are contractible.
* Equivalences

A singleton is a type consisting of just one element. In set theory,
if $a$ is an element of a set $A$, then the singleton set is $\{a\}$,
which we could write more explicitly as $\{ x ∈ A ∣ a = x \}$. We can
give an analogous definition of singletons in type theory using pair
types.

```
singl : {A : Type ℓ} → (a : A) → Type ℓ
singl {A = A} a = Σ[ x ∈ A ] a ≡ x
```

There is a unique element of `singl a`, namely the pair `(a, refl)`
which says that `a` is itself.

```
singlBase : (a : A) → singl a
singlBase a = (a , refl)
```

We would like to say in type theory that `singl a` has a unique
element, so we need a way of expressing "has a unique element"
type-theoretically. For this, we use:

```
∃! : Type ℓ → Type ℓ
∃! A = Σ[ x ∈ A ] (∀ y → x ≡ y)
```

In words, to give an element of `∃! A` we must give an element `x : A`
and then a function assigning to every `y : A` a path `x ≡ y`. This
means that `A` has a unique element, where we are saying two elements
are the same by virtue of the paths between them.

Homotopically speaking, this means that the type `A` *contracts onto
`x`*. So, if we have an element of `∃! A`, we say that `A` is
*contractible*. This terminology is more common in homotopy type
theory, so we record it here as well.
```
isContr : Type ℓ → Type ℓ
isContr A = ∃! A

center : {A : Type ℓ} → isContr A → A
center c = fst c

contraction : {A : Type ℓ} (c : isContr A) (a : A) → center c ≡ a
contraction c = snd c
```

We should expect that singletons should be have a unique element,
which is to say that singletons should be contractible.
```
{- Hint: A square is necessary in the second component, draw it and
complete the definition.

Super Hint: It's exactly the connection square
             p
         y - - - > y
         ^         ^
    refl |         | p            ^
         |         |            j |
         x — — — > y              ∙ — >
            refl                    i
-}
isContrSingl : (a : A) → isContr (singl a)
-- Exercise
isContrSingl a = (a , refl) , contract
  where
    contract : (y : singl a) → (a , refl) ≡ y
    contract (x , p) = {!!}
```

We show that our type `⊤`, which was defined to have only a single
element `tt : ⊤`, is contractible.

```
isContr⊤ : isContr ⊤
-- Exercise
isContr⊤ = {!!}
```

Any two contractible types are isomorphic. As a corollary, any
contractible type is isomorphic to `⊤`.

```
isContr→Iso : {A : Type ℓ} {B : Type ℓ'} → isContr A → isContr B → Iso A B
-- Exercise
-- isContr→Iso c c' = ?
isContr→Iso c c' = {!!}

isContrIso⊤ : {A : Type}  → isContr A → Iso A ⊤
isContrIso⊤ c = isContr→Iso c isContr⊤
```

We can show that the converse is true: if `A` is isomorphic to `⊤`,
then it is contractible.

```
iso⊤IsContr : {A : Type ℓ} → Iso A ⊤ → isContr A
-- Exercise
iso⊤IsContr the-iso = {!!}
  where
    f = Iso.fun the-iso
    g = Iso.inv the-iso
    s = Iso.rightInv the-iso
    r = Iso.leftInv the-iso
```


We can show that there is in fact a unique map from `∅` to any type.
```
∅-rec-unique : {A : Type ℓ} → isContr (∅ → A)
-- ∅-rec-unique = ?
∅-rec-unique = {!!}
```


As a useful lemma, we can show that a retract of a contractible type must be contractible.
```
isContrRetract
  : ∀ {A : Type ℓ} {B : Type ℓ'}
  → (f : A → B) (g : B → A)
  → (h : retract f g)
  → (v : isContr B) → isContr A
-- Exercise
-- Hint: You'll need transitivity of paths.
fst (isContrRetract f g h (b , p)) = {!!} 
snd (isContrRetract f g h (b , p)) = {!!} 
```

And we can show that if `B : A → Type` is a family of contractible types depending on `A`, then the type `(a : A) → B a` of functions is contractible.
```
isContrFun : ∀ {A : Type ℓ} {B : A → Type ℓ}
           → ((a : A) → isContr (B a))
           → isContr ((a : A) → B a)
-- Exercise
fst (isContrFun c) = {!!}
snd (isContrFun c) f i a = {!!}
```

In particular, there is a unique map `A → ⊤`.

## Equivalences

In set theory, a bijection between sets $A$ and $B$ is a function
$f : A → B$ where for every $b ∈ B$, there is a unique $a ∈ A$ such
that $f(a) = b$. We can define an analogous notion in type theory:

```
isBijection : {A B : Type ℓ} (f : A → B) → Type ℓ
isBijection {A = A} f = ∀ b → ∃! (Σ[ a ∈ A ] (f a ≡ b))
```

As with "∃!" and "contractible", the names in type theory are taken
from homotopy theory. Here are the usual names in type theory:

First, we define the "fiber" of a function f : A → B, which is the
type theoretic name for "inverse image". In homotopy theory, this
would be called the "homotopy fiber".

```
fiber : {A : Type ℓ} {B : Type ℓ'} (f : A → B) (y : B) → Type (ℓ-max ℓ ℓ')
fiber {A = A} f y = Σ[ x ∈ A ] (f x ≡ y)
```

Then, instead of saying that a function is a "bijection", we will say
that it is an "equivalence" when it has contractible fibers.

```
isEquiv : {A : Type ℓ} {B : Type ℓ'} (f : A → B) → Type (ℓ-max ℓ ℓ')
isEquiv {B = B} f = (y : B) → isContr (fiber f y)
```

We note that bijection and equivalence are the exact same notion, just
packaged together slightly different.

```
isBijection≡isEquiv : {A B : Type ℓ} (f : A → B) → isBijection f ≡ isEquiv f
isBijection≡isEquiv f = refl
```

We will use the syntax `A ≃ B` (≃ is input as \simeq) for the type of
equivalences between `A` and `B`.

```
infix 4 _≃_

_≃_ : (A : Type ℓ) (B : Type ℓ) → Type ℓ
A ≃ B = Σ[ f ∈ (A → B) ] isEquiv f
```

The identity function is an equivalence. This comes down to fact that
the fiber of the identity function over of point `a` is the singleton at
`a` (or, it would be, if the cubical library hadn't made the inscrutable
choice to flip the direction of the path in the definition of
fiber...).

```
singl' : {A : Type} (a : A) → Type
singl' {A = A} a = Σ[ x ∈ A ] (x ≡ a)

isContrSingl' : {A : Type} (a : A) → isContr (singl' a)
-- Exercise
isContrSingl' a = (a , refl) , contract
  where
    contract : (y : singl' a) → (a , refl) ≡ y
    contract (x , p) i = {!!}

idIsEquiv : (A : Type) → isEquiv (idfun A)
idIsEquiv A = λ y → isContrSingl' y

idEquiv : (A : Type) → A ≃ A
idEquiv A = idfun A , idIsEquiv A
```


From any equivalence, we can extract an isomorphism.
```
inv : {A B : Type} → A ≃ B → B → A
inv e b = fst (center (snd e b))

equivToIso : {A B : Type} → A ≃ B → Iso A B
-- Exercise
equivToIso e = iso (fst e) (inv e) (s e) (r e)
  where
    s : (e : A ≃ B) → section (fst e) (inv e)
    s (e , is-equiv) y = {!!}

    r : (e : A ≃ B) → retract (fst e) (inv e)
    r (e , is-equiv) x i = {!!}
```

There is in fact a way to turn an iso into an equivalence as well, but
it is much more involved. We will take it as a black box for now, and
later import it from the cubical library.

```
-- isoToIsEquiv : (f : Iso A B) → isEquiv (Iso.fun f)
```

You might naturally wonder if `Iso A B` and `A ≃ B` are themselves
isomorphic. This turns out not to be the case! The reason is that
there are types with multiple distinct paths between the same
elements --- we will sometimes call these "higher types", and we'll
see them later on in Part 2.

Consider the type of ways to show that the identity function `idfun X
: X → X` is an isomorphism: that is, functions `f : X → X` with `s :
(x : X) → f x ≡ x` and `r : (x : X) → f x ≡ x`. If `X` is a higher
type, then it may be that there are two different paths `p q : f x ≡
x` --- that is, that the type `p ≡ q` of paths between `p` and `q` is
empty. In this case, we might end up with different ways of giving
functions `s` and `r`.

On the other hand, no matter how complicated the type `X` is,
`isEquiv (idfun X)` is always a contractible type; that is, the
identity function is an equivalence in exactly one way. We will show
this in Part 2-5.


## Relations

A (type-valued) *relation* between two types `A` and `B` is a type
family `R : A → B → Type` depending on both `A` and `B`. We interpret
the type `R a b` as "the type of ways that `a` relates to `b`".

(There is some futzing around with universe levels, since `Rel A B` is
a type of type families and so must live at a higher universe level
than both of the input types.)

```
Rel : ∀ {ℓ} {ℓ'} (A : Type ℓ) (B : Type ℓ') → Type (ℓ-suc (ℓ-max ℓ ℓ'))
Rel {ℓ} {ℓ'} A B = A → B → Type (ℓ-max ℓ ℓ')
```

Any function `f : A → B` induces a relation `graph f : Rel A B` known
as the graph of `f`.

```
graph : {A B : Type ℓ} → (A → B) → Rel A B
graph f a b = (f a ≡ b)
```

This says that the ways we relate `a : A` and `b : B` via the graph of
`f` are precisely the paths from `f a` to `b` (in `B`). The graph is a
special sort of relation: it is a "functional relation". A relation
`R : Rel A B` is functional if for every `a : A`, there is a unique `b :
B` and way `r : R a b` that `a` relates with `b`.

```
isFunctional : {A B : Type ℓ} → Rel A B → Type ℓ
isFunctional {B = B} R = ∀ a → ∃! (Σ[ b ∈ B ] (R a b))
```

The graph of a function is a functional relation --- hence the name.
```
isFunctionalGraph : {A B : Type ℓ} (f : A → B) → isFunctional (graph f)
-- Exercise:
-- isFuncationalGraph f a = ?
isFunctionalGraph f a = {!!}
```

On the other hand, any functional relation gives rise to a function.
```
isFunctional→Fun : {A B : Type ℓ} (R : Rel A B) (c : isFunctional R)
                 → A → B
-- Exercise:
-- isFunctional→Fun R c a = ?
isFunctional→Fun R c a = {!!}
```

We can show that the function we extract out of the graph of a
function `f` is just `f`:
```
section-isFunctionalGraph→Fun : {A B : Type} (f : A → B)
      → isFunctional→Fun (graph f) (isFunctionalGraph f) ≡ f
-- Exercise:v
-- section-isFunctionalGraph→Fun f = ?
section-isFunctionalGraph→Fun f = {!!}
```

We can show that, in the other direction, we get an isomorphism
between `R a b` and `(graph (isFunctional→Fun R c)) a b` whenever `R`
is a functional relation. But we don't have quite the tools yet, we'll have to revisit it in the next lecture.

For every relation `R : Rel A B`, we have a relation `flip R : Rel B A`
defined by `(flip R) b a = R a b`. A relation is said to be a
*one-to-one correspondence* if both it and its flip are functional;
that is, if for every `a` there is a unique `b` and `r : R a b` and
for every `b` there is a unique `a` and `r : R a b`.

```
flip : {A : Type ℓ} {B : Type ℓ'} {C : A → B → Type ℓ''} →
       ((x : A) (y : B) → C x y) → ((y : B) (x : A) → C x y)
flip f y x = f x y

isOneToOne : {A B : Type} (R : Rel A B) → Type _
isOneToOne R = isFunctional R × isFunctional (flip R)
```

If `e : A ≃ B` is an equivalence, then its graph is a one-to-one correspondence.
```
graphEquivIsOneToOne : {A B : Type} (e : A ≃ B)
                     → isOneToOne (graph (fst e))
-- Exercise
-- graphEquivIsOneToOne e = ?
graphEquivIsOneToOne (e , p) = {!!}
```

We can also go the other way, but we'll need a few more tools in our toolbelt.
