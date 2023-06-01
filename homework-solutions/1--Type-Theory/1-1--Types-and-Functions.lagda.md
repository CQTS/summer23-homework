# Homework 1-1: Types and Functions

```
module homework-solutions.1--Type-Theory.1-1--Types-and-Functions where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Sigma.Base

```

Topics covered:

* Types and Elements
* (Dependent) Function Types and Function Composition
* (Dependent) Pair Types

A type theory is a formal system for keeping track of what type of
thing every mathematical object is. This idea is familiar from
computer science; since everything in a computer is stored as a chunk
of bits (values which may either be 0 or 1), it is important to record
what any given chunk of bits is supposed to mean. Is this chunk of
bits meant to be a number? Or a piece of text? Maybe it's meant to be
a program. Since all of these things are ultimately stored as a bunch
of bits, if we don't keep track of how we were supposed to use them we
run the risk of accidentally considering some text as a very large
number and adding it to another number.

When we say that some piece of data is "meant" to be a number, what we
mean is that we intend to use it like a number -- maybe add or
multiply it with other numbers. A type theory, then, is a formal
language for keeping track of our intentions with data.

In this course, we will focus on mathematical aspects of type
theory. With an expressive enough language for describing our
intentions with data, it turns out that we can formalize essentially
all of mathematics. The basic work of mathematics --- defining
concepts and structures, constructing examples, stating and proving
propositions --- can all be expressed in the lanaguge of the
particular type theory we will be using: a variant of Martin-Löf type
theory called Cubical Type Theory.

Agda is a program that acts as a "proof assistant" for writing down
arguments in Cubical Type Theory. The file you are reading right now
is a literate Agda file: all the lines between the triple backticks
are actual Agda code that can be loaded by pressing C-c C-l.

The basic statement of any type theory is "this `a` is an `A`" or
"this thing `a` has that type `A`". We write this symbolically using a
colon `a : A`. In the expression `a : A`, `A` is the "type" and `a` is
the "element".

The vast majority of any Agda file consists of definitions, which have
two parts. First, a declaration that gives a fresh (i.e. unused)
identifier together with the type that we want it to have. Second, a
list of equations that define the actual meaning of the identifier.

```
three : ℕ      --- This line declares that "three" is a natural number.
three = 3      --- This line defines "three" to be the number 3
               --- We'll see how 3 is defined in the next lecture.
```

(In this case, there is only one equation, but we will soon see
examples with more than one.)

## Functions

In the next lecture, we'll see how to define specific types of data
like bits (Booleans) and numbers. For this lecture, we'll focus on the
most fundamental concept in type theory: functions.

A function `f : A → B` may be thought of in two ways:

* 1: An operation which takes an element `x : A` as input and produces
  an element `f(x) : B` as output.
* 2: An element `f(x) : B` whose definition involves a variable element
  `x : A`.

Here is our first Agda function: the identity function of type `ℕ → ℕ`.
```
idℕ : ℕ → ℕ
idℕ x = x 
```

Functions are defined by placing a fresh variable name to the left of
the `=` sign, which can then be used on the right. So here, idℕ
accepts `x` as input, and immediately produces `x` as output.

Here is another way to define the identity function:
```
idℕ' : ℕ → ℕ
idℕ' = λ (x : ℕ) → x
```

The syntax `λ (x : A) → t` defines the function `A → B` which sends `x` to
`t`, where `t : B` is some expression potentially involving `x`. This way of
defining functions is sometimes called "anonymous function
declaration", since it doesn't require naming the function. The lambda
symbol λ comes to us by way of Church's λ-calculus, an early formal
system for defining functions intended as a model of general
computability.

To write the λ in Emacs, enter "\Gl" or "\lambda". If you ever forget
how to write a symbol, you can type "M-x describe-char" with the
cursor on the symbol to find out what it takes to write: look at the "to
input:" line of the resulting window. Try this out by figuring out how
to write ⊗.

We can write functions of multiple arguments by giving functions of
single arguments that themselves return functions. This technique is
called "currying" after the computer scientist Haskell Curry (whose
name is also immortalized in the programming language
Haskell). Consider the following two functions:
```
constℕ : ℕ → ℕ → ℕ
constℕ a b = a

constℕ' : ℕ → (ℕ → ℕ)
constℕ' a = λ b → a
```

These two functions are identical to Agda, but the way we have written
them suggests the two different ways we might think of functions of
multiple arguments:

* The function `constℕ` is written as a function of two variables `a` and
  `b`, returning the first.
* The function `constℕ'` is written as a function of a single variable `a`,
  returning the function `ℕ → ℕ` which takes `b : ℕ` and yields `a`.

Later in this lecture, we will see another (more familiar) way to see
a function of two arguments `x` and `y` as a function of their pair
`(x , y)`.

We can apply a function `f : A → B` to an argument `a : A` by writing
`f a : B` --- note the lack of parentheses around `a`!

```
applyℕ : (ℕ → ℕ) → ℕ → ℕ
applyℕ f a = f a
```

Note that while we didn't need the parentheses around `(ℕ → ℕ)` in the
definition of `const` (it is the same as const', where we did write the
parentheses), here it is important that we put `(ℕ → ℕ)` in
parentheses. This is because we are taking the function `f : ℕ → ℕ` as
an argument to `apply`.


The functions we have written are all specialised to only work with
elements of the type `ℕ`. This is overly restrictive, we should have
an identity function `A → A` that works for any type `A` at all.

```
idE : (A : Type) → A → A
idE A x = x
```

Let's understand why the type of `id` is a bit more complicated than
just `A → A`.  The extra bit `(A : Type) →` is there because the type
`A → A` itself involves a variable: `A` itself. For this reason, we
must say that `A` is a type, which we do by writing `A : Type`. This
`A` is then an additional argument to the function, so it also appears
on the left of the `=` in the definition.

If we think in terms of currying, `id` a function of a variable `A`,
which is a type. When applied, `id A` gives back the identity function
`A → A` for that type.

`const` and `apply` can be similarly generalised:
```
constE : (A : Type) → (B : Type) → A → B → A
constE A B a b = a

applyE : (A : Type) → (B : Type) → (A → B) → A → B
applyE A B f a = f a
```

There is one more trick before we reach the definition of `id`,
`const` and `apply` that we will actually use. It is necessary for
these functions to have arguments that determine the types that are
used in the output, but in some sense they are redundant. For example,
the `x` argument to `id` is of type `A`, so if we know `Inductive-x`, we know
what `A` had to be.

Agda lets us make these arguments implicit, so they are reconstructed
from the other arguments. This is done by surrounding them with curly
braces rather than parentheses:
```
id : {A : Type} → A → A
id x = x

const : {A : Type} → {B : Type} → A → B → A
const a b = a

apply : {A : Type} → {B : Type} → (A → B) → A → B
apply f a = f a

ev : {A : Type} → {B : Type} → A → (A → B) → B
ev a f = f a
```
This saves a huge amount of typing in the long run. Agda will complain
if it cannot reconstruct an implicit argument given the other
arguments you have provided.

We can compose functions by applying the second to the result of the
first. Try implementing it:
```
compose : {A : Type} {B : Type} {C : Type}
    → (B → C)
    → (A → B)
    → (A → C)
-- Exercise:
-- compose g f = {!!}
compose g f = λ a → g (f a)
```

Agda considers definitions with underscores specially, and lets us
refer to such a definition in to ways: either the normal way, that is,
`_∘_ g f`, or with the arguments replacing the underscores: `g ∘ f`.
We will use infix operators like this whenever it is closer to normal
mathematical practice, like this composition operator or arithmetical
operators `+`, `·`, etc.

Try implementing the following functions.

```
flip : {A B C : Type}
     → (A → B → C)
     → (B → A → C)
-- Exercise:
-- flip = {!!}
flip f y x = f x y

-- Should use the provided function on the argument twice.
apply-twice : {A : Type}
     → (A → A)
     → A
     → A
-- Exercise:
-- apply-twice = {!!}
apply-twice f x = f (f x)
```

* Pen and paper exercise: Check that `f ∘ id` and `id ∘ f` act the
 same as `f` on any argument. In Part 2 of this course, we'll be able
 to express that fact in theory and have Agda verify that it is
 correct!

## Dependent types and dependent functions

We can think of a function `f : A → B` as an element `f x : B`
depending on an element `x : A` for its definition. We can also have
types which depend on elements for their definition.

As a mathematical example, let `k : ℕ` be a number consider the type
`{n : ℕ ∣ k ≤ n}` of numbers at least as big as `k`. This is a type,
but to define it we make use of a variable element of `ℕ`. In total,
we would have `(λ (k : ℕ) → { n : ℕ ∣ k ≤ n }) : ℕ → Type` --- a
function valued in a type of types. We will often call a function with
shape `A → Type` a "type family over `A`".

Just as we have a type `A → B` of functions from `A` to `B`, if `B : A → Type`
is a type family depending on `x : A`, then we have a type of
dependent functions `(x : A) → (B x)` which send an element `x : A` to an
element `(f x) : B x`.

We will sometimes think of the dependent function type as a
generalised cartesian product. In a function with type `(x : A) → (B
x)`, the `x : A` acts like an index, and then for each index we have
an element of the corresponding type. If `A` has exactly two elements
`0` and `1`, say, then `(x : A) → (B x)` is the binary cartesian
product of `B 0` and `B 1`.

mvrnote: this is confusing I think
```
Π : (A : Type) → (B : A → Type) → Type
Π A B = (x : A) → B x
```

Note that most of the functions in this file have already been
dependent function types! In `id : {A : Type} → A → A`, the type `A →
A` depends on `{A : Type}`, so this is a dependent function using the
type family

```
id-family : Type → Type
id-family A = A → A
```

Here is the full dependent composition.
```
_∘_ : ∀ {A : Type} {B : A → Type} {C : (x : A) → B x → Type} (g : {a : A} → (b : B a) → C a b) → (f : (a : A) → B a) → (a : A) → C a (f a)
g ∘ f = λ x → g (f x)
```
## Pair types

The other basic type forming operation we have is the type of pairs,
written `×`. The pair of `a : A` and `b : B`, is writte `(a , b)`,
which is an element of `A × B`. The space before the comma is
necessary, or Agda thinks you are referring to a variable called `a,`.

```
pair× : {A : Type} → {B : Type} → A → B → (A × B)
pair× a b = (a , b)
```

To use a pair, we can "project out" the first and second components
using the in-built funtions `fst` and `snd`.

```
my-fst× : {A : Type} → {B : Type} → (A × B) → A
my-fst× p = fst p

my-snd× : {A : Type} → {B : Type} → (A × B) → B
my-snd× p = snd p
```

These can be chained together to work with nested pairs.

```
triple× : {A B C : Type} → A → B → C → ((A × B) × C)
triple× a b c = ((a , b) , c)

my-fst×× : {A B C : Type} → ((A × B) × C) → A
my-fst×× t = fst (fst t)

my-snd×× : {A B C : Type} → ((A × B) × C) → B
my-snd×× t = snd (fst t)

my-trd×× : {A B C : Type} → ((A × B) × C) → C
my-trd×× t = snd t
```

With pair types we can make precise the currying and uncurrying idea
from earlier, going from a function with a single argument that is a
pair, to a function that returns a function, and vice versa.

```
curry× : {A B C : Type}
  → ((A × B) → C)
  → (A → (B → C))
curry× f x y = f (x , y)

uncurry× : {A B C : Type}
  → (A → (B → C))
  → ((A × B) → C)
uncurry× f p = f (fst p) (snd p)
```

There is nothing special about functions of two arguments here, try
writing similar functions for a function of three arguments:

```
curry3 : {A B C D : Type}
  → (((A × B) × C) → D)
  → (A → B → C → D)
-- Exercise:
-- curry3 f = {!!}
curry3 f x y z = f ((x , y) , z)

uncurry3 : {A B C D : Type}
  → (A → B → C → D)
  → (((A × B) × C) → D)
-- Exercise:
-- uncurry3 f = {!!}
uncurry3 f t = f (fst (fst t)) (snd (fst t)) (snd t)
```

Just as type theory generalises function types to dependent function
types, it also generalises pair types to dependent pair types, so the
type of the second component of the pair type is allowed to depend on
the value in the first component. If `A : Type` and `B : A → Type`,
then the dependent pair type is written `Σ[ x ∈ A ] B x`. These pair
types are used just like the non-dependent pair types, only the types
involved have changed:

```
pairΣ : {A : Type} → {B : A → Type} → (x : A) → B x → Σ[ x ∈ A ] (B x)
pairΣ a b = (a , b)

my-fstΣ : {A : Type} → {B : A → Type} → Σ[ x ∈ A ] (B x) → A
my-fstΣ p = fst p

my-sndΣ : {A : Type} → {B : A → Type} → (p : Σ[ x ∈ A ] (B x)) → B (fst p)
my-sndΣ p = snd p
```

The type of `snd` is a little complicated! When we form `snd p`, the
type we get is determined by the value of `B: A → Type` at `fst p`. To
express that in the type of `my-sndΣ`, we have to need to use a
dependent function so that the result type `B (fst p)` can refer to
the pair `p`.

`curry` and `uncurry` can ge generalised to work with dependent pairs
and functions.

mvrnote: exercise?

```
uncurry : {A : Type} → {B : A → Type} → {C : (x : A) → B x → Type}
  → ((x : A) → (y : B x) → C x y)
  → (p : Σ[ x ∈ A ] B x) → C (fst p) (snd p)
uncurry f p = f (fst p) (snd p)

curry : {A : Type} → {B : A → Type} → {C : (x : A) → B x → Type}
  → ((p : Σ[ x ∈ A ] B x) → C (fst p) (snd p))
  → (x : A) → (y : B x) → C x y
curry f x y = f (x , y)
```

Finally in this section, we have the "universal mapping property" of
pairs: functions `C → A × B` correspond exactly with pairs of
functions `C → A` and `C → B`.

```
×-ump : {A B C : Type}
      → (C → A)
      → (C → B)
      → (C → A × B)
-- Exercise:
-- ×-ump = {!!}
×-ump f g c = (f c , g c)
```

We will have a lot to say about universal properties in this course.

## Extras 1. Universe Levels

We might ask what type the type `Type` of types has. It turns out that
asserting `Type : Type` is contradictory thanks to some
"Russell-style" paradoxes. For this reason, we instead have "universe
levels", usually written ℓ, that stratify types into a
heirarchy. `Type` on its own is secretly `Type₀` the type of all types
at level zero. But `Type₀` itself does not live at level zero, but one
step up: `Type₀ : Type₁`. Similarly, `Type₁ : Type₂`, and so on. In
general, `Type ℓ : Type (ℓ-suc ℓ)` for any level ℓ, where `ℓ-suc` is a
built in function that increments a level by one.

All our above functions involving types can be further generalised to
work for types in any universe level.
```
idℓ : ∀ {ℓ} {A : Type ℓ} → A → A
idℓ x = x
```
But we won't need to make use of this for a while.
