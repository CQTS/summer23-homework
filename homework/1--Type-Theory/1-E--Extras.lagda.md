# 1-- Extras

```
module homework.1--Type-Theory.1-E--Extras where

-- In order to use the Agda builting naturals, we will be importing from the cubical library instead of the data types defined in this course

open import Cubical.Foundations.Prelude using (Type)
open import Cubical.Data.Nat
open import Cubical.Data.Bool hiding (_≤_)
open import Cubical.Data.List using (List ; [] ; _++_)
                              renaming (_∷_ to _::_)
```

This is a file of extra practice problems. Most of them are about lists.

```
-- A list containing just one entry
[_] : {A : Type} → A → List A
[ a ] = a :: []
```

Before we start, the list recursion principle has a special name: fold
```
fold : {A B : Type}
     → (start : B)        -- the starting value
     → (acc : A → B → B)  -- the accumulating function
     → List A → B
fold start acc [] = start
fold start acc (x :: L) = acc x (fold start acc L)
```

```
-- Use fold to write a function that sums a list of numbers
-- sumℕ [1, 2, 3, 4] should be 10
sumℕ : List ℕ → ℕ
sumℕ = {!!}

-- To test that you did it right, try normalizing the following test
-- To normalize, use C-c C-n, then type in test-sum.
-- Or, write test-sum in any hole and C-c C-n there.
test-sum : ℕ
test-sum = sumℕ (1 :: 2 :: 3 :: 4 :: [])

-- Now dow a product
-- prodℕ [1, 2, 3, 4] should be 24
prodℕ : List ℕ → ℕ
prodℕ = {!!}

test-prod : ℕ
test-prod = prodℕ (1 :: 2 :: 3 :: 4 :: [])
```

```
-- Write a function which filters a list according to a proposition:
-- filter isEven [1, 2, 3, 4, 5, 6] should be [2, 4, 6]
filter : {A : Type} → (A → Bool) → List A → List A
filter p L = {!!}

filter-test : List ℕ
filter-test = filter isEven (1 :: 2 :: 3 :: 4 :: 5 :: 6 :: [])

```

```
-- Write a function which reverses a list
-- reverse [1, 2, 3, 4] should be [4, 3, 2, 1]
reverse : {A : Type} → List A → List A
reverse L = {!!}

reverse-test : List ℕ
reverse-test = reverse (1 :: 2 :: 3 :: 4 :: [])
```

```
-- Write a fuction which applies a function to each element in a list
-- map suc [1,2,3,4] should be [2, 3, 4, 5]
map : {A B : Type} → (A → B) → List A → List B
map f L = {!!}

map-test : List ℕ
map-test = map suc (1 :: 2 :: 3 :: 4 :: [])
```

```
-- This one is more difficult...
-- Write a function which sorts a list.
-- sort _≤_ [5,3,1,2,4] should be [1,2,3,4,5]
{-# NON_TERMINATING #-} -- This scary thing will just stop Agda whining
                        -- about the expected solution.
                        -- If you're curious about why agda is whining,
                        -- Ask me sometime
                        -- (or look into well founded recursion).
sort : {A : Type} (_leq_ : A → A → Bool) → List A → List A
sort _leq_ L = {!!}

_≤_ : ℕ → ℕ → Bool
zero ≤ m = true
suc n ≤ zero = false
suc n ≤ suc m = n ≤ m

sort-test : List ℕ
-- This will only normalize if you do C-c C-n outside a hole
sort-test = sort _≤_ (5 :: 3 :: 1 :: 2 :: 4 :: [])

```



