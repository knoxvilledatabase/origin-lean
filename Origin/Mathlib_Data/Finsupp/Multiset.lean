/-
Extracted from Data/Finsupp/Multiset.lean
Genuine: 2 of 4 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Equivalence between `Multiset` and `ℕ`-valued finitely supported functions

This defines `Finsupp.toMultiset` the equivalence between `α →₀ ℕ` and `Multiset α`, along
with `Multiset.toFinsupp` the reverse equivalence and `Finsupp.orderIsoMultiset` (the equivalence
promoted to an order isomorphism).

-/

open Finset

variable {α β ι : Type*}

namespace Finsupp

def toMultiset : (α →₀ ℕ) →+ Multiset α where
  toFun f := Finsupp.sum f fun a n => n • {a}
  -- Porting note: have to specify `h` or add a `dsimp only` before `sum_add_index'`.
  -- see also: https://github.com/leanprover-community/mathlib4/issues/12129
  map_add' _f _g := sum_add_index' (h := fun _ n => n • _)
    (fun _ ↦ zero_nsmul _) (fun _ ↦ add_nsmul _)
  map_zero' := sum_zero_index

theorem toMultiset_add (m n : α →₀ ℕ) : toMultiset (m + n) = toMultiset m + toMultiset n :=
  toMultiset.map_add m n
