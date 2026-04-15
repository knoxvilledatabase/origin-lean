/-
Extracted from CategoryTheory/Category/PartialFun.lean
Genuine: 2 of 5 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# The category of types with partial functions

This defines `PartialFun`, the category of types equipped with partial functions.

This category is classically equivalent to the category of pointed types. The reason it doesn't hold
constructively stems from the difference between `Part` and `Option`. Both can model partial
functions, but the latter forces a decidable domain.

Precisely, `PartialFunToPointed` turns a partial function `α →. β` into a function
`Option α → Option β` by sending to `none` the undefined values (and `none` to `none`). But being
defined is (generally) undecidable while being sent to `none` is decidable. So it can't be
constructive.

## References

* [nLab, *The category of sets and partial functions*]
  (https://ncatlab.org/nlab/show/partial+function)
-/

open CategoryTheory Option

universe u

def PartialFun : Type (u + 1) := Type u

namespace PartialFun

-- INSTANCE (free from Core): :

def of : Type* → PartialFun :=
  id

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): largeCategory
