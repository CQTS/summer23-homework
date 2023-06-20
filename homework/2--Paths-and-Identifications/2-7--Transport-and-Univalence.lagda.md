# Homework 2-7: Transport and Univalence
```
module homework.2--Paths-and-Identifications.2-7--Transport-and-Univalence where

open import Cubical.Data.Sigma.Base

open import homework.1--Type-Theory.1-1--Types-and-Functions
open import homework.1--Type-Theory.1-2--Inductive-Types
open import homework.1--Type-Theory.1-3--Propositions-as-Types
open import homework.2--Paths-and-Identifications.2-1--Paths hiding (cong)
open import homework.2--Paths-and-Identifications.2-2--Path-Algebra-and-J
open import homework.Library.Univalence
open import homework.2--Paths-and-Identifications.2-4--Composition-and-Filling
open import homework.2--Paths-and-Identifications.2-5--Propositions
open import homework.2--Paths-and-Identifications.2-6--Sets
open import homework.Library.EquationalReasoning

open import Cubical.Core.Glue public
  using (Glue ; glue ; unglue)

private
  variable
    ℓ ℓ' : Level
    A B C : Type ℓ

```

https://1lab.dev/1Lab.Path.html#transport

In this lecture, we will revisit `transport`, and see that paths in the
type `Type` of types are equivalences between types.

## Transport

First, we'll note that `transport p : A → B` for `p : A ≡ B` is an
equivalence between `A` and `B`. We can prove this cleverly, by
transporting the proof that the identity function is an equivalence.
```
isEquivTransport : {A B : Type ℓ} (p : A ≡ B) → isEquiv (transport p)
isEquivTransport {A = A} p =
  transport (λ i → isEquiv (λ x → transport-filler p x i)) (idIsEquiv A)

pathToEquiv : {A B : Type ℓ} → A ≡ B → A ≃ B
fst (pathToEquiv p) = transport p
snd (pathToEquiv p) = isEquivTransport p
```

As we noted at the end of 2-5, paths in subtypes can be computed in
the underlying type. Since the type `A ≃ B` of equivalences is a
subtype of the type of functions `A → B` (since `A ≃ B` is by
definition `Σ[ f ∈ A → B ] isEquiv f` and `isEquiv f` is a
proposition), we may compute paths between equivalences on their
underlying functions. We recall this here:
```
isProp→PathP : ∀ {B : I → Type ℓ} → ((i : I) → isProp (B i))
               → (b0 : B i0) (b1 : B i1)
               → PathP B b0 b1
isProp→PathP {B = B} hB b0 b1 = toPathP (hB i1 (transp B i0 b0) b1)

isPropIsEquiv : (f : A → B) → isProp (isEquiv f)
-- The appearance of `equiv-proof` is an artifact of the way the core
-- Agda library defines `isEquiv`. With our definition, the
-- construction would be simply
-- `isPropIsEquiv f u0 u1 i y = isPropIsContr (u0 y) (u1 y) i`
equiv-proof (isPropIsEquiv f u0 u1 i) y = isPropIsContr (u0 .equiv-proof y) (u1 .equiv-proof y) i

equivEq : {e f : A ≃ B} → (h : e .fst ≡ f .fst) → e ≡ f
equivEq {e = e} {f = f} h = λ i → (h i) , isProp→PathP (λ i → isPropIsEquiv (h i)) (e .snd) (f .snd) i
```

An easy application is that the constant path `refl` at a type `A`
becomes us the identity equivalence on `A`.
```
pathToEquivRefl : {A : Type ℓ} → pathToEquiv refl ≡ idEquiv A
pathToEquivRefl {A = A} = equivEq (λ i x → transp (λ _ → A) i x)
```

Here are some examples of transporting in paths of types. If the path
of types is constant at an inductive type such as `ℕ` or `Bool`, then
transporting is simply the identity.

```
_ : {x : ℕ} → transport (λ i → ℕ) x ≡ x
_ = refl

_ : {b : Bool} → transport (λ i → Bool) b ≡ b
_ = refl
```

In general, however, transporting over a constant path is not by
definition the identity.
```
{- Error!
_ : {x : A} → transport (λ _ → A) x ≡ x
_ = refl
-}
```

In the basic type formers that we have (pairs, functions, paths),
`transport` in the compound type is computes to some combination of
`transport`s in the input types.
```
-- First, non-dependent:
module _ {A : I → Type} {B : I → Type} where private
```

To transport in a type of pairs, we just transport in each component:
```
  _ : {x : A i0} {y : B i0}
    →   transport (λ i → A i × B i) (x , y)
      ≡ (transport (λ i → A i) x , transport (λ i → B i) y)
  _ = refl

```

To transport in a type of functions, we transport *backwards* along
the domain, then apply the function, and then transport forwards along
the codomain:
```
  _ : {f : A i0 → B i0}
    →   transport (λ i → A i → B i) f
      ≡ λ x → transport (λ i → B i) (f (transport (λ i → A (~ i)) x))
  _ = refl
```

This is because `f : A i0 → B i0`, but `transport (λ i → A i → B i) f`
has to be a function `A i1 → B i1`, so to apply `f` to an element of
`A i1`, we first need to pull it back to `A i0`.

We can mix and match these. Here is how a "`B`-valued binary operation
on `A`" would transport:
```
  _ : {m : A i0 × A i0 → B i0}
    → transport (λ i → A i × A i → B i) m
    ≡ λ {(x , y) →
      let
        x' = (transport (λ i → A (~ i)) x)
        y' = (transport (λ i → A (~ i)) y)
      in transport (λ i → B i) (m (x' , y'))}
  _ = refl
```

Here's how a function into `Bool` would transport:
```
  _ : {p : A i0 → Bool}
    → transport (λ i → A i → Bool) p
    ≡ λ x → p (transport (λ i → A (~ i)) x)
  _ = refl
```

Try it yourself:
```
  _ : {m : A i0 × A i0 → A i0}
    → transport (λ i → A i × A i → A i) m
    ≡ {!!}
  _ = refl

  _ : {α : A i0 × B i0 → B i0}
    → transport (λ i → A i × B i → B i) α
    ≡ {!!}
  _ = refl

  _ : {y : (A i0 → A i0) → A i0}
    → transport (λ i → (A i → A i) → A i) y
    ≡ {!!}
  _ = refl
```

There are dependent versions of the above computation rules for
`transport`. They follow the same pattern as above, but further
work is necessary so that things still typecheck.
```
module _ {A : I → Type} {B : (i : I) → A i → Type} where private
  _ : {x0 : A i0} {y0 : B i0 x0}
    → transport (λ i → Σ[ x ∈ A i ] B i x) (x0 , y0)
    ≡ let
          -- This is just the same as in the non-dependent case
          x1 : A i1
          x1 = transport (λ i → A i) x0

          -- Here we need a path from `B i0 x0` to `B i1 x1`
          y1 = transport {!!} y0
        in (x1 , y1)
  _ = refl

  _ : {f : (x0 : A i0) → B i0 x0}
    → transport (λ i → (x : A i) → B i x) f
    ≡ λ (x1 : A i1) →
        let
          x0 : A i0
          x0 = transport (λ i → A (~ i)) x1

          fx1 : B i1 x1
          fx1 = transport {!!} (f x0)
        in fx1
  _ = refl

```

Finally, `transport` in a path type becomes a (double) composition,
the top of the following square:


               a i1 ∙ ∙ ∙ ∙ ∙ ∙ > b i1
                ^                   ^
                |                   |              ^
                |                   |            j |
          tr A (a i0) — — — > tr A (b i0)          ∙ — >
                                                     i

This is now a square entirely in the type `A i1`, and so the
`transport` may compute further depending on what `A i1` is.

```
module _ {A : I → Type} {a : (i : I) → A i} {b : (i : I) → A i} where private
  _ : {p : a i0 ≡ b i0}
    → transport (λ i → a i ≡ b i) p
    ≡ {!!}
  _ = refl

```

`PathP` is similar, but we have to write the `hcomp` manually, becuase
`doubleComp` is only defined for ordinary paths.
```
module _ {A : I → I → Type} {a : (i : I) → A i i0} {b : (i : I) → A i i1} where private
  _ : {p : PathP (A i0) (a i0) (b i0)}
    → transport (λ i → PathP (A i) (a i) (b i)) p
    ≡ λ j → hcomp (λ i → λ { (j = i0) → fromPathP (λ i → a i) i;
                             (j = i1) → fromPathP (λ i → b i) i } )
            (transport (λ i → A i j) (p j))
  _ = refl

```

## Glue Types and Univalence

An important feature of Cubical Type Theory is *univalence*. This is
the statement that paths between types are equivalent to equivalences
between those types.

Cubical Type Theory's central accomplishment over other type theories
is allowing the univalence principle to compute. This is done using -
in addition to all the cubical machinery we've seen so far - *Glue*
types, whose constructor has the following signature.

`Glue : (A : Type ℓ) {φ : I}
       → (Te : Partial φ (Σ[ T ∈ Type ℓ' ] T ≃ A))
       → Type ℓ'`

`Glue` is a type constructor that takes a type `A`, a formula `φ`, and
a partial element `Te : Partial φ (Σ[ T ∈ Type ] (T ≃ A))` of pairs of
types equipped with an equivalence to `A`. The type we are taking
partial elements of, `Σ[ T ∈ Type ] (T ≃ A)`, is reminiscent of the
singleton types from 2-3; if `(T ≃ A)` were equivalent to `(T ≡ A)`,
then this would be the singleton type of `A` in `Type`.

As usual, the formula `φ` plays a crucial role. Consider the case of
`φ = ∂ i`. We can depict an element of the partial type
`Te : Partial (∂ i) (Σ[ T ∈ Type ℓ' ] T ≃ A)` as follows:

                 A i
         A i0  - - - > A i1
           ^             ^
    Te i0  (             ( Te i1                  ^
           )             )                        )
         T i0          T i1                       ∙ — >
                                                    i

where the vertical lines are equivalences, rather than paths. This
looks a lot like the kind of thing we were `hcomp`ing over in 2-4
(except that it is open on the bottom rather than the top, which is a
conventional choice --- the equivalences go into `A`, rather than out
of it). `Glue` types enable us to "cap off" this open box of types.

That is, if `φ = ∂ i`, then `Glue A Te : Type` is the line of types
living *under* `A` in the capped off version of the above square.

`Glue` types come with some guarantees. Firstly, like `hcomp`, the
line that we get agrees with the partial input anywhere the formula
`φ` holds. In the example, this means `Glue A Te = T i0` when `i = i0`
and `Glue A Te = T i1` when `i = i1`.

Secondly, for any element of `Glue A Te` at all, we can extract the
underlying element of `A` that we started with: this is called
`unglue φ : Glue A Te → A`. Because of the above computation rule, if we
are working where `φ` holds then the domain of this function is `T`.
Luckily, if `φ` holds, we have access to an equivalence `T ≃ A`, from
which we can extract the necessary function `T → A`.

To summarise, `Glue Te` is a version of `A` that has the types `T`
glued on wherever `φ` holds, using the provided equivalences `Te` to
extract an underlying element of `A` when asked.

The first and most important example of a `Glue` type gives us
"univalence".

           B
      B - - - > B
      ^         ^
    e (         ( idEquiv                ^
      )         )                        )
      A         B                        ∙ — >
                                           i

```
ua : A ≃ B → A ≡ B
ua {A = A} {B = B} e i = Glue B {φ = ∂ i} (λ { (i = i0) → (A , e)
                                             ; (i = i1) → (B , idEquiv B) })
```

We can show that `ua` of the identity equivalence is `refl`.
```
uaIdEquiv : ua (idEquiv A) ≡ refl
uaIdEquiv {A = A} i j = Glue A {φ = i ∨ ∂ j} (λ _ → A , idEquiv A)
```

And, nicely, transporting over `ua e` is the same as applying `e`.
```
uaβ : (e : A ≃ B) (x : A) → transport (ua e) x ≡ fst e x
uaβ e x = transportRefl (equivFun e x)
```

For concrete types this typically holds definitionally, like
`transport`, but for an arbitrary equivalence `e` between abstract
types `A` and `B` we have to prove it. This is an instance of the
computation rule for `transport` on `Glue` types, which in general is
quite complicated.

```
uaβBool : (e : Bool ≃ Bool) (x : Bool) → transport (ua e) x ≡ fst e x
uaβBool e x = refl

_ : transport (ua (isoToEquiv not-Iso)) true ≡ false
_ = refl

uaβS¹ : (e : S¹ ≃ S¹) (x : S¹) → transport (ua e) x ≡ fst e x
uaβS¹ e x = refl
```

`unglue` works as expected on `ua` - we are able to get out the
element of `B` no matter where we are in the `Glue` type `ua e i`.
```
ua-unglue : ∀ (e : A ≃ B) (i : I) (x : ua e i) → B
ua-unglue e i x = unglue (∂ i) x

_ :  ∀ {A B : Type ℓ} (e : A ≃ B) (i : I) (x : ua e i0) → ua-unglue e i0 x ≡ (fst e) x
_ = λ e i x → refl

_ :  ∀ {A B : Type ℓ} (e : A ≃ B) (i : I) (x : ua e i1) → ua-unglue e i1 x ≡ x
_ = λ e i x → refl
```

If ‵x : A` and `y : B`, then to get a `PathP` from `x` to `y` over `ua
e i` is the same as giving a path from `e x` to `y`.
```

ua-PathP→Path : ∀ (e : A ≃ B) {x : A} {y : B}
              → PathP (λ i → ua e i) x y
              → e .fst x ≡ y
ua-PathP→Path e p i = ua-unglue e i (p i)
```

Finally, univalence is an isomorphism, and so we have completely
characterised paths between types.
```
au : A ≡ B → A ≃ B
au = pathToEquiv

ua-au : (p : A ≡ B) → ua (au p) ≡ p
ua-au = J (λ _ p → ua (au p) ≡ p) path
  where path = ua (au refl)   ≡⟨ cong ua pathToEquivRefl ⟩
               ua (idEquiv _) ≡⟨ uaIdEquiv ⟩
               refl ∎

au-ua : (e : A ≃ B) → au (ua e) ≡ e
au-ua e = equivEq (funExt (uaβ e))

univalenceIso : Iso (A ≡ B) (A ≃ B)
univalenceIso .Iso.fun = au
univalenceIso .Iso.inv = ua
univalenceIso .Iso.rightInv = au-ua
univalenceIso .Iso.leftInv = ua-au
```

Here is an interesting application: we can implement addition in `ℤ`
as composition of paths, and addition with any fixed integer must be
an equivalence.

```
sucℤ-Path : ℤ ≡ ℤ
sucℤ-Path = isoToPath sucℤ-Iso

add-n-Path : ℕ → ℤ ≡ ℤ
add-n-Path zero = refl
add-n-Path (suc n) = add-n-Path n ∙ sucℤ-Path

predℤ-Path : ℤ ≡ ℤ
predℤ-Path = isoToPath (invIso sucℤ-Iso)

sub-n-Path : ℕ → ℤ ≡ ℤ
sub-n-Path zero = refl
sub-n-Path (suc n) = sub-n-Path n ∙ predℤ-Path

_+ℤ'_ : ℤ → ℤ → ℤ
m +ℤ' pos n    = transport (add-n-Path n) m
m +ℤ' negsuc n = transport (sub-n-Path (suc n)) m

-- This agrees with regular addition defined by pattern-matching
+ℤ'≡+ℤ : _+ℤ'_ ≡ _+ℤ_
+ℤ'≡+ℤ i m (pos zero) = m
+ℤ'≡+ℤ i m (pos (suc n)) = sucℤ (+ℤ'≡+ℤ i m (pos n))
+ℤ'≡+ℤ i m (negsuc zero) = predℤ m
+ℤ'≡+ℤ i m (negsuc (suc n)) = predℤ (+ℤ'≡+ℤ i m (negsuc n))

-- So +ℤ' with a fixed element is an equivalence
isEquivAddℤ' : (m : ℤ) → isEquiv (λ n → n +ℤ' m)
isEquivAddℤ' (pos n)    = isEquivTransport (add-n-Path n)
isEquivAddℤ' (negsuc n) = isEquivTransport (sub-n-Path (suc n))

isEquivAddℤ : (m : ℤ) → isEquiv (λ n → n +ℤ m)
isEquivAddℤ = subst (λ add → (m : ℤ) → isEquiv (λ n → add n m)) +ℤ'≡+ℤ isEquivAddℤ'
