# Homework 2-4: Composition and Filling
```
module homework-solutions.2--Paths-and-Identifications.2-4--Composition-and-Filling where

open import Cubical.Core.Primitives
open import Cubical.Foundations.Function using (_∘_; const; _$_)

open import homework-solutions.1--Type-Theory.1-2--Inductive-Types
open import homework-solutions.1--Type-Theory.1-3--Propositions-as-Types
open import homework-solutions.2--Paths-and-Identifications.2-1--Paths
open import homework-solutions.2--Paths-and-Identifications.2-2--Path-Algebra-and-J
open import homework-solutions.2--Paths-and-Identifications.2-3--Uniqueness-and-Equivalence


private
  variable
    ℓ ℓ' ℓ'' : Level
    A B C D : Type ℓ
    S : A → Type ℓ
    x y z w : A
```

References:

* https://1lab.dev/1Lab.Path.html

Cubical Agda adds a number of primitive notions that make working with
paths between paths easier. To understand how they work, we will
really have to start putting the "cubical" in Cubical Agda.


## Prelude: Boolean Partial Elements

In this lecture, we will learn about partial elements (open boxes) and
composition (filling boxes). But to understand how partial elements
work with the interval, it will be worth exploring an analogue in the
more familiar Boolean world.

First, let's revisit our function `Bool→Type : Bool → Type` which
converted a Boolean into a type. Let's rename this function here so
that the analogy will become clearer later when we learn about partial
elements over the interval.

```
IsTrue : Bool → Type
IsTrue true = ⊤
IsTrue false = ∅

trueIsTrue : IsTrue true
trueIsTrue = tt
```

A Boolean partial element of a type `A` is an element of `A` which
exists only conditionally, with the condition being some Boolean `φ`.
```
BooleanPartial : Bool → Type → Type
BooleanPartial φ A = IsTrue φ → A
  -- if φ then A else ⊤
```

Any fully defined element of `A` is also a partially defined one: if
it always exists, then it certainly still exists when `φ` is `true`.

```
just : {A : Type} {φ : Bool} → A → BooleanPartial φ A
just a = λ _ → a
```

And there's always the completely undefined element: we only need to
give an `A` in the case that `φ` is `true`, which certainly never
happens if `φ` is `false`.

```
nothing : {A : Type} → BooleanPartial false A
nothing = ∅-rec
```

Now, you might wonder at the utility of these definitions. After all,
if `φ` is `true`, then `BooleanPartial φ A` is `⊤ → A`, which is
isomorphic to `A`. If `φ` is `false`, then `BooleanPartial φ A` is `∅
→ A`, which is isomorphic to `⊤`. In other words, this type is either
isomorphic to `A` or `⊤`, depending on whether or not `φ` is `true` or
`false` --- what's the big deal?

The reason that `BooleanPartial` is an interesting type is because
when we use it, we don't think of `φ` as representing a single Boolean
value; we think of `φ` as representing a Boolean *formula*. That is,
we will usually be using this type *in context*, and in that case, `φ`
can be some formula involving other Booleans (or, other things
entirely).

Consider the function which divides a natural number evenly in two,
for example.
```
-- halfOf : Σ[ n ∈ ℕ ] IsTrue (isEven n)  → ℕ
halfOf : (n : ℕ) → BooleanPartial (isEven n) ℕ
halfOf zero = just zero                  -- half of 0 is 0
halfOf (suc zero) = nothing              -- half of 1 is not defined
halfOf (suc (suc n)) = suc ∘ (halfOf n)  -- half of (n + 2) is one more than half of n.
```

This function cannot produce a natural number on every input, since
not every input can be divided evenly in two. We can, however, think
of `halfOf n` as a partially defined element of `ℕ`; specifically,
`halfOf n` is a partially defined natural number which is well defined
if `isEven n` is `true` - or, in other words, if we have
`trueIsTrue : IsTrue (isEven n)`, using our definitions above.


Here's another example of a partially defined element, which shows
that what can happen when `φ` is a Boolean formula.
```
zeroOrOnePartial : (b : Bool) → BooleanPartial (b or (not b)) ℕ
zeroOrOnePartial true = just zero
zeroOrOnePartial false = just (suc zero)
```

We can ask whether a partial element `p` *extends* to an entire (fully
defined) element `x`. That is, is there an `x : A` so that `p ≡ just
x`? In this case, we say that "`x` *extends* `p`". For `zeroOrOne` we
can say the answer is yes.

```
zeroOrOneTotal : Bool → ℕ
zeroOrOneTotal true = zero
zeroOrOneTotal false = suc zero

doesItExtend : zeroOrOnePartial ≡ just ∘ zeroOrOneTotal
doesItExtend i true = just zero
doesItExtend i false = just (suc zero)
```

In the case of `halfOf` above, the answer is no --- not every natural
number can be evenly divided in half. We say that a partial element is
*extensible* if it can be extended to a full element.

Aside: here's a fun exercise in Boolean partial functions. Write a
function which takes the first `n` elements of a list - as long as it
has at least `n` elements.

```
_≤_ : ℕ → ℕ → Bool
zero ≤ m = true
suc n ≤ zero = false
suc n ≤ suc m = n ≤ m

take : (n : ℕ) (L : List A) → BooleanPartial (n ≤ length L) (List A)
-- Exercise
take zero L = just []
take (suc n) [] = nothing
take (suc n) (x :: L) = (x ::_) ∘ (take n L)
```

## Partial elements

Now we come to partial elements defined on intervals. As we saw in
2-2, the interval `I` has the structure of a De Morgan algebra. This
lets us write down logical looking formulas with cubical variables,
like `i ∨ (j ∧ ~ k)`. Thinking of `I` as the topological unit interval
$[0, 1]$, this formula is meant to represent the function
$\max(x, \min(y, 1 - z))$; thinking logically, it seems to say
"i or (j and not k)". As it turns out, we can think in both ways.

Just like with the Booleans, we will say that a formula like
`i ∨ (j ∧ ~ k)` is "true" when it equals `i1`. This corresponds to a
subset of the cube $[0,1]³$, namely, the set
$\{ (x, y, z) ∣ \max(x, \min(y, 1 - z)) = 1 \}$.
We can therefore think of these interval formulas as describing
"subsets of cubes `Iⁿ`" - even though `I` isn't actually a set that we
can take subsets of.

For example, the formula `i ∨ ~ i` (which appears to say "i or not i")
should correspond to the subset $\{ x ∈ [0, 1] ∣ \max(x, 1-x) = 1 \}$,
which a bit of thinking shows is set of endpoints $\{0, 1\} ⊆ [0 , 1]$
of the unit interval. Likewise for us, we will think of the formula
`i ∨ ~ i` as defining the part of the interval consisting only of the
endpoints `i0` and `i1`.

Agda has a primitive type former `Partial φ A` where `φ : I` is an
element of the interval - but thought of as a formula - and `A` is a
type. Thinking of `φ` as describing some part of some cube, we can
think of `Partial φ A` as the functions from that shape to `A`.

We can see that `i ∨ ~ i` really behaves like the part of the interval
consisting only of the endpoints by defining a `Partial` element on it:
```
--- trueOrFalse is the function on {i0, i1} to Bool which sends i0 to true and i1 to false.
trueOrFalse : (i : I) → Partial (i ∨ ~ i) Bool
trueOrFalse i (i = i0) = true
trueOrFalse i (i = i1) = false
```

We can't write a function `I → Bool` into a *total* element of `Bool`
which is `true` on `i0` and `false` on `i1`; there is no way to jump
from `true` to `false` as we move along the interval (as we proved in
`true≢false`). But because the partial element only has to be defined
on the endpoints, we can say what the values of `trueOrFalse` on those
endpoints are and not worry about what happens in between.

Since `i ∨ ~ i` is a common pattern, it's reasonable to give it a
name. We call it `∂ i`, since `∂` typically means "boundary" in
mathematics.

```
∂ : I → I
∂ i = i ∨ ~ i
```

As a more interesting partial element, consider an open box:

        .         .
        ^         ^
        |         |          ^
        |         |        j |
        . — — — > .          ∙ — >
                               i

The open box above is part of a square, so we are in the context of
two interval variables `i j : I'. Now we need to figure out how to
describe the open box as an "interval valued formula", which is to
say, as a function into `I'.

```
open-box : I → I → I
open-box i j =
-- (continued below)
```
We want an expression `open-box i j : I` which equals `i1` just when
`i` and `j` are constrained to be in the open box. Now, `i` and `j`
are in the open box if they are in the left of the box, the right of
the box, or the bottom of the box. So our `φ i j` will be the "union"
```
  (left-of-box i j) ∨ (right-of-box i j) ∨ (bottom-of-box i j)
  where
   left-of-box : I → I → I
   right-of-box : I → I → I
   bottom-of-box : I → I → I
```
Now, `i` and `j` are in the left of the box just when `i = i0`, or in
other words when `~ i = i1`. So
```
   left-of-box i j = ~ i
```
Similarly, `i` and `j` are in the right of the box when `i = i1`, so
```
   right-of-box i j = i
```
Finally, `i` and `j` are in the bottom of the box when `j = i0`, or
when `~ j = i1`, so
```
   bottom-of-box i j = ~ j
```
This completes our definition of the function `open-box : I → I → I`:
`open-box i j = ~ i ∨ i ∨ ~ j`.

Try it yourself: describe a formula which gives the two sides of a box

        .         .
        ^         ^
        |         |          ^
        |         |        j |
        .         .          ∙ — >
                               i

```
sides-of-square : I → I → I
-- Exercise
sides-of-square i j = ∂ i
```

How about a three dimensional example. Come up with a formula to
describe this part of the cube consisting of the bottom face and three
of the sides.

                .                   .
              / ^                 / ^
            /   |               /   |
          /     |             /     |
        . - - - - - - - - > .       |
        ^       |           ^       |                    ^   j
        |       |           |       |                  k | /
        |       |           |       |                    ∙ — >
        |       |           |       |                      i
        |       . - - - - - | - - > .
        |     /             |     /
        |   /               |   /
        | /                 | /
        . - - - - - - - - > .

```
exercise-shape : I → I → I → I
-- Exercise
exercise-shape i j k = ~ i ∨ i ∨ ~ j ∨ ~ k 

exercise-shape-wireframe : I → I → I → I
exercise-shape-wireframe i j k =
  ((~ i ∧ (∂ j ∨ ∂ k))) ∨ (i ∧ (∂ j ∨ ∂ k))
  ∨ (~ j ∧ (∂ i ∨ ∂ k)) ∨ ~ k ∧ (∂ i ∨ ∂ j)
```

## Extensibility and Composition

As with Boolean partial elements we can ask whether a partial element
defined on some part of a cube can extend to the whole cube. The
partial element `trueOrFalse` above definitely cannot extend to a
whole element, since a whole element `p i : Bool` for `i : I` for
which `p i0 = true` and `p i1 = false` would be a path `true ≡ false`
- and this would give us an element of the empty type!

However, Cubical Agda bakes in some guarantees that a partial element
can be extended. In short, Cubical Agda allows us to "close off open
boxes" using an operation called `hcomp` (which stands for
"homogeneous composition").

Aside: It's worth noting that we can't extend a partial element using
`hcomp` in *any* type. The types for which `hcomp` works are called
*fibrant* types, taking a name from homotopy theory. Essentially all
the types we use in practice are fibrant; every element of a type
universe `Type ℓ` is fibrant. But some back-end plumbing types are not
fibrant --- they live in a universe called `SSet` for "strict set".
We'll see an example in a bit.

Let's see an example, which will also be an important operations on
paths: path composition. The most natural notion of homogeneous path
composition in a cubical setting is double composition which composes
three paths in a line:

          w ∙ ∙ ∙ > z
          ^         ^
    sym r |         | q        ^
          |         |        j |
          x — — — > y          ∙ — >
               p                 i

We can represent this open box on the left as a partial element in the
following way:
```
doubleComp-tube : {A : Type ℓ} {x y z w : A}
                  (r : w ≡ x) (p : x ≡ y) (q : y ≡ z)
                   (i j : I) → Partial (open-box i j) A
doubleComp-tube r p q i j (i = i0) = (sym r) j
doubleComp-tube r p q i j (i = i1) = q j
doubleComp-tube r p q i j (j = i0) = p i
```
We want to cap off this box to get a path `w ≡ z`. To do this, we need
to put it in another form which we can apply `hcomp`. Speaking
loosely, we will have

* `hcomp (the sides of the box) (the full bottom face) = (the full top face)`


Here, the sides of the box are a partial path in the context of
`i j : I` which is only defined when `i` is either `i0` or `i1`.

          w         z
          ^         ^
    sym r |         | q        ^
          |         |        j |
          x         y          ∙ — >
                                 i
```
doubleComp-sides : {x y z w : A } (r : w ≡ x) (q : y ≡ z)
                   (i j : I) → Partial (∂ i) A
-- doubleComp-faces r q is a partial square defined only on ∂ i
doubleComp-sides r q i j (i = i0) =
  (sym r) j  -- when i = i0, it is sym r
doubleComp-sides r q i j (i = i1) =
  q j        -- when i = i1, it is q
```

The bottom of the box is `p`. Therefore, we can use `hcomp` to close
off the box. We will call the top of this particular box the "double
composite".
```
_∙∙_∙∙_ : (r : w ≡ x) (p : x ≡ y) (q : y ≡ z) → w ≡ z
(r ∙∙ p ∙∙ q) i = hcomp (doubleComp-sides r q i) (p i)
```

Here we can see what `hcomp` really takes as input: first, a "partial
path" of types `I → Partial φ A` which we can think of as the side of
the box that sits over a point on the bottom of the box. In this case,
this is `doubleComp-sides r q i : I → Partial (∂ i) A` which is the
side of the box (going up vertically) which sits over the point
indexed by `i` on the bottom of the box.

Second, `hcomp` takes a (full) point on the bottom of the box, here
`p i`. Agda will check that these two inputs play nice, which means
that when we take the sides of the box and plug in `j = i0` (so that
we're looking at the part of the sides which intersects the bottom),
we will get some partial element `Partial φ A` of the bottom of the
box which agrees with the element on the bottom that we put in when
`φ` is true.

In this case, that means that `doubleComp-sides r q i i0`, an element
of `Partial (∂ i) A`, has to agree with `p i` on `∂ i`, which is to
say when `i = i0` or `i = i1`. This obviously works in our case since
`doubleComp-sides r q i i0` was by definition `p i` --- though
remember that this was `p i : Partial (∂ i) A`, which is to say its
the partial element `p i` defined only when `i = i0` or `i = i1`.

We can use pattern matching lambdas to inline the definition of the
sides of the box when doing an `hcomp`. This is the same as separately
defining the sides.

```
doubleComp' : (r : w ≡ x) (p : x ≡ y) (q : y ≡ z) → w ≡ z
doubleComp' {x = x} r p q i =
  hcomp (λ { j (i = i0) → (sym r) j
           ; j (i = i1) → q j       })
        (p i)                            

-- This is identical to the previous definition.
_ : (r : w ≡ x) (p : x ≡ y) (q : y ≡ z)
  → (r ∙∙ p ∙∙ q) ≡ (doubleComp' r p q)
_ = λ r p q → refl
```

More formally we can see that `hcomp` takes in two arguments:

* A partially defined path `sides : (j : I) → Partial φ A`, representing side of the box sitting
  over a point in the bottom face. Note that `φ` can't involve `j` --- this means that while the sides may not be defined everywhere on the bottom of the box, they always go all the way from bottom to top (in particular, no floating points). Above, this is
  `doubleComp-sides r q i : (j : I) → Partial (∂ i) A`,
  which is a path in `A` that is only defined when `i` (which indexes
  a point in the bottom of the box) is `i0` or `i1`.

* A element of `A` representing the entire bottom of the box. This can
  vary over interval variables in the context, and so doesn't have to
  be a constant square.


We can produce a filler for the whole square using `hfill`

            r ∙∙ p ∙∙ q
          w - - - - - - > z
          ^               ^
    sym r |  ...-filler   | q        ^
          |               |        j |
          x - — — — - - > y          ∙ — >
                  p                    i

```
doubleCompPath-filler' : (r : w ≡ x) (p : x ≡ y) (q : y ≡ z)
                      → Square (sym r) q p (r ∙∙ p ∙∙ q)
doubleCompPath-filler' r p q i j =
  hfill (doubleComp-sides r q i) (inS (p i)) j
```

As you can see, the `hfill` here at first takes in the same two
arguments as the `hcomp` we used, and then the interval variable in
the direction we are trying to fill. But there is something
interesting in the second argument: `inS`. To understand what `inS`
is, we need to discuss extension types.

Extension types are not *fibrant* types, meaning that we can't use
`hcomp` in them. They are really a part of the back-end cubical
plumbing. If `φ` is a formula and `u : Partial φ A` is a partial
element, then we can form the extension type `A [ φ ↦ u ]` which is
the type of all *full* elements of `A` that definitionally equal `u`
when the formula `φ` holds. In other words, an element of `A [ φ ↦ u ]`
is an element of `A` about which we know some definitional
constraints.

We've seen types that work like this before: paths. A path `p : x ≡ y`
is a function `I → A` about which we know that `p i0 = x` and
`p i1 = y`. Using extension types, we could write this as

```
endpoints : ∀ {A : Type ℓ} (x y : A) → (i : I) → Partial (∂ i) A
endpoints x y i (i = i0) = x
endpoints x y i (i = i1) = y

Path-ish : ∀ {A : Type ℓ} (x y : A) → SSet ℓ
Path-ish {A = A} x y = (i : I) → A [ ∂ i ↦ endpoints x y i ]
```

Given a partial element `e : (i : I) → Partial (∂ i) A` defined only
when `i = i0` or `i = i1` --- the endpoints of our path --- we get a
"strict set" (element of `SSet`) consisting of the functions
`p : I → A" where by definition `p i0 = endpoints i0` and
`p i1 = endpoints i1`.

The path type isn't exactly the same thing as our `Path-ish` above,
for the simple reason that path types are in fact *fibrant*; we have
`x ≡ y : Type`.

Now we can come to `inS`. This is the function that takes a full
element `a : A` and gives us `inS a : A [ φ ↦ (λ _ → a) ]`. In other
words, it tells us that any full element can be seen as the extension
of any partial restriction of it.

Finally, we can understand the type of `hfill`. We have, roughly speaking,

"`hfill (the (partially defined) side of the box over a point in the base)
        (a (full) element of the base extending the bottom of the sides)
        (an element of the interval, "pointing up")`"


For some inscrutable reason, the definition used in the Cubical
library is actually diagonally flipped to this (which we can achieve
by exchanging the two interval arguments.)

               q
          y - - - > z
          ^         ^
       p  |         | r ∙∙ p ∙∙ q          ^
          |         |                    j |
          x — — — > w                      ∙ — >
             sym r                           i
```
doubleCompPath-filler : (r : w ≡ x) (p : x ≡ y) (q : y ≡ z)
                      → Square p (r ∙∙ p ∙∙ q) (sym r) q
doubleCompPath-filler r p q j i =
  hfill (doubleComp-sides r q i) (inS (p i)) j
```

We are now ready to define composition of paths.

            p ∙ q
          x ∙ ∙ ∙ > z
          ^         ^
     refl |         | q        ^
          |         |        j |
          x — — — > y          ∙ — >
               p                 i

```
_∙_ : x ≡ y → y ≡ z → x ≡ z
p ∙ q = refl ∙∙ p ∙∙ q
```

Remark: it seems like we shouldn't really need to use the left side of
the box in this definition. The following code should be a fine way to
define the composite:

```
{- Error!
_∙∙_ : x ≡ y → y ≡ z → x ≡ z
(p ∙∙ q) i = hcomp (λ { j (i = i1) → q j }) (p i)
-}
```
The problem here is that this also has to fill in the left side of the
box, and when it does it gets `hcomp (λ ()) x` in the top left
corner. This is not by definition `x`, so this fails to give us a path
`x ≡ z`. This is similar to the fact that transporting over `refl` does
not give us the identity function definitionally.

We also have the filler for composition (which is also diagonally
flipped in the library.)

               q
          y - - - > z
          ^         ^
       p  |         | p ∙ q                ^
          |         |                    j |
          x — — — > x                      ∙ — >
             refl                            i

```
compPath-filler : (p : x ≡ y) (q : y ≡ z) → Square p (p ∙ q) refl q
compPath-filler p q = doubleCompPath-filler refl p q
```

## Constructing Cubes

Let's do an example of a (3-d) cube. Let's say we want to construct
this square:

            q
       y - - - > z
       ^         ^
     p |         | q            ^
       |         |            j |
       x — — — > y              ∙ — >
            p                     i

```
diamond : (p : x ≡ y) (q : y ≡ z) → Square p q p q
```

To construct this via an `hcomp`, we need to cook up a cube (using an
extra dimension `k`) with this square as the top face, and where we
already know fillers for all the remaining sides.

                          q
                y - - - - - - - - > z
          p   / ^             q   / ^
            /   |               /   |
          /     |   p         /     |
        x - - - - - - - - > y       |
        ^       |           ^       |                    ^   j
        |       |           |       |                  k | /
        |       |           |       |                    ∙ — >
        |       |           |       |                      i
        |       ? - - - - - | - - > ?
        |  ?  /             |     /
        |   /               |   /  ?
        | /                 | /
        ? - - - - - - - - > ?
                  ?

We can make some educated guesses about what will work as the bottom
face. The bottom-left corner should be `x`, because `refl` is the only
immediately available path that ends in `x`. Similarly, the two
bottom-middle corners should be `x` or `y`. If we choose `x`, then two
of the resulting faces will involve all of `x`, `y` and `z`, so in the
hope of keeping thing simpler we go with `y`. Finally, if the
bottom-right corner is `z`, then the bottom face is exactly the thing
we are trying to construct, so to make progress we must go with `y`:


                          q
                y - - - - - - - - > z
          p   / ^             q   / ^
            /   |               /   |
          /     |   p         /     |
        x - - - - - - - - > y       |
        ^       |           ^       | q                  ^   j
        |       |           |       |                  k | /
        |       |           |       |                    ∙ — >
        |       |           |       |                      i
        |       y - - - - - | - - > y
        |  p  /             |     /
        |   /               |   /
        | /                 | /
        x - - - - - - - - > y
                  p

Now we have, in fact, seen all of these faces before (except the top
one.)
```
diamondFaces : {x y z : A} (p : x ≡ y) (q : y ≡ z) → (i : I) → (j : I) → I → Partial (∂ i ∨ ∂ j) A
-- Exercise
diamondFaces p q i j k (i = i0) = p j
diamondFaces p q i j k (i = i1) = q (j ∧ k)
diamondFaces p q i j k (j = i0) = p i
diamondFaces p q i j k (j = i1) = q (i ∧ k)

-- Exercise
diamond p q i j = hcomp (diamondFaces p q i j) (p (i ∨ j))
```

This is not the only way to do it! The composition problems that
result in some desired square are not unique. Try constructing the
same `diamond` square, but using the following cube:

                          q
                y - - - - - - - - > z
          p   / ^             q   / ^
            /   |               /   |
          /     |   p         /     |
        x - - - - - - - - > y       |
        ^       |           ^       | p ∙ q              ^   j
        |       | p         |       |                  k | /
        |       |           |       |                    ∙ — >
        |       |           | p     |                      i
        |       x - - - - - | - - > x
        |     /             |     /
        |   /               |   /
        | /                 | /
        x - - - - - - - - > x


```
diamondFacesAlt : {x y z : A} (p : x ≡ y) (q : y ≡ z) → (i : I) → (j : I) → I → Partial (∂ i ∨ ∂ j) A
-- Exercise
diamondFacesAlt p q i j k (i = i0) = p (j ∧ k)
diamondFacesAlt p q i j k (i = i1) = compPath-filler p q j k
diamondFacesAlt p q i j k (j = i0) = p (i ∧ k)
diamondFacesAlt p q i j k (j = i1) = compPath-filler p q i k

diamondAlt : (p : x ≡ y) (q : y ≡ z) → Square p q p q
diamondAlt {x = x} p q i j = hcomp ((diamondFacesAlt p q i j)) x
```

Let's set about proving associativity for path composition. To prove
associativity, we will use the same trick as above and construct a
cube whose top face is the path-between-paths that we want.

                              refl
                      z - - - - - - - - > z
                    / ^                 / ^
     r ∙ (p ∙ q)  /   |               /  (r ∙ p) ∙ q
                /     | refl        /     |
              w - - - - - - - - > w       |
              ^       |           ^       | q                  ^   j
              |     q |           |       |                  k | /
              |       |           |       |                    ∙ — >
              |       |   refl    |       |                      i
              |       y - - - - - | - - > y
             r ∙ p  /             |     /
              |   /               |   /  r ∙ p
              | /                 | /
              w - - - - - - - - > w
                      refl

```
assoc-faces : {w x y z : A} (r : w ≡ x) (p : x ≡ y) (q : y ≡ z) → (i : I) → (j : I) → (k : I) → Partial (∂ i ∨ ∂ j) A
-- Exercise
assoc-faces         r p q i j k (i = i0) = (r ∙ (compPath-filler p q k)) j
assoc-faces         r p q i j k (i = i1) = compPath-filler (r ∙ p) q k j
assoc-faces {w = w} r p q i j k (j = i0) = w
assoc-faces         r p q i j k (j = i1) = q k

assoc-base : {w x y z : A} (r : w ≡ x) (p : x ≡ y) (q : y ≡ z) → Square (r ∙ p) (r ∙ p) refl refl
-- Exercise
assoc-base r p q i j = (r ∙ p) j

assoc : (r : w ≡ x) (p : x ≡ y) (q : y ≡ z)
  → r ∙ (p ∙ q) ≡ (r ∙ p) ∙ q
assoc r p q i j = hcomp (assoc-faces r p q i j) (assoc-base r p q i j)
```

We can also prove that `refl` is the unit for path composition. That
`refl` can be cancelled on the right is exactly one of the above
filler squares.

           refl
        y - - - > z
        ^         ^
     p  |         | p ∙ refl             ^
        |         |                    j |
        x — — — > w                      ∙ — >
           refl                            i
```
rUnit : (p : x ≡ y) → p ≡ p ∙ refl
rUnit p i j = compPath-filler p refl i j
```

To cancel on the left we have to build another cube.

                y - - - - - - - - > y
              / ^                   ^
         p  /   |                   |
          /     |                   |
        x - - - - - - - - > x       |
        ^       |           ^       | p                  ^   j
        |       |           |       |                  k | /
        |       |           |       |                    ∙ — >
        |       |   sym p   |       |                      i
        |       y - - - - - | - - > x
        |  p  /             |     /
        |   /               |   / refl
        | /                 | /
        x - - - - - - - - > x
                refl

The faces are straightforward to construct if you stare at the diagram.
Rather nicely, `hcomps` are *uniform*. That means that if we do an `hcomp` on some shape and then restrict to a subshape, the result is the same as restricting and doing the `hcomp` there. In the above cube, since the `i = i1` face is exactly the square from the `hcomp` defining `refl ∙ p`, we can omit it from our final `hcomp`.
```
lUnit-faces : {x y : A} (p : x ≡ y) → (i : I) → (j : I) → (k : I) → Partial (~ i ∨ ∂ j) A
lUnit-faces         p i j k (i = i0) = p j -- Constant in the `k` direction
-- We can omit the (i = i1) direction, since it will be filled in
-- by the appropriate value
lUnit-faces {x = x} p i j k (j = i0) = x -- Completely constant
lUnit-faces         p i j k (j = i1) = p (~ i ∨ k) -- Constructed from `p` using connections

lUnit-base : {x y : A} (p : x ≡ y) → Square p refl refl (sym p)
-- Hint: Constructed from `p` using connections in a different way
lUnit-base p i j = p (~ i ∧ j)

lUnit : (p : x ≡ y) → p ≡ refl ∙ p
lUnit {x = x} p i j = hcomp (lUnit-faces p i j) (lUnit-base p i j)
```

Here's an open ended problem that requires using two `hcomps`. Try and figure out what boxes you should try and close off to solve it.

```
isContrisContr≡ : {A : Type ℓ} (c : isContr A) (a b : A) → isContr (a ≡ b)
-- Hint: You should use an `hcomp` for both halves. Draw them out!
-- Hint 2: In the second component, you only need three sides of a cube.
fst (isContrisContr≡ (c₀ , c) a b) i =
  hcomp (λ { j (i = i0) → c a j
           ; j (i = i1) → c b j })
        c₀ 
snd (isContrisContr≡ (c₀ , c) a b) p i j =
   hcomp (λ { k (i = i1) → c (p j) k 
            ; k (j = i0) → c a k
            ; k (j = i1) → c b k}) c₀
```
