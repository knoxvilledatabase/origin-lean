/-
Extracted from Order/Lex.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Type synonyms

This file provides two type synonyms for order theory:

* `Lex α`: Type synonym of `α` to equip it with its lexicographic order. The precise meaning depends
  on the type we take the lex of. Examples include `Prod`, `Sigma`, `List`, `Finset`.
* `Colex α`: Type synonym of `α` to equip it with its colexicographic order. The precise meaning
  depends on the type we take the colex of. Examples include `Finset`, `DFinsupp`, `Finsupp`.

## Notation

The general rule for notation of `Lex` types is to append `ₗ` to the usual notation.

## Implementation notes

One should not abuse definitional equality between `α` and `αᵒᵈ`/`Lex α`. Instead, explicit
coercions should be inserted:

* `Lex`: `toLex : α → Lex α` and `ofLex : Lex α → α`.
* `Colex`: `toColex : α → Colex α` and `ofColex : Colex α → α`.

## See also

This file is similar to `Mathlib.Algebra.Group.TypeTags.Basic`.
-/

assert_not_exists OrderDual

variable {α : Type*}

/-! ### Lexicographic order -/

def Lex (α : Type*) :=
  α
