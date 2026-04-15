/-
Extracted from Data/Sigma/Order.lean
Genuine: 2 of 4 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Orders on a sigma type

This file defines two orders on a sigma type:
* The disjoint sum of orders. `a` is less `b` iff `a` and `b` are in the same summand and `a` is
  less than `b` there.
* The lexicographical order. `a` is less than `b` if its summand is strictly less than the summand
  of `b` or they are in the same summand and `a` is less than `b` there.

We make the disjoint sum of orders the default set of instances. The lexicographic order goes on a
type synonym.

## Notation

* `_root_.Lex (Sigma α)`: Sigma type equipped with the lexicographic order.
  Type synonym of `Σ i, α i`.

## See also

Related files are:
* `Data.Finset.CoLex`: Colexicographic order on finite sets.
* `Data.List.Lex`: Lexicographic order on lists.
* `Data.Pi.Lex`: Lexicographic order on `Πₗ i, α i`.
* `Data.PSigma.Order`: Lexicographic order on `Σₗ' i, α i`. Basically a twin of this file.
* `Data.Prod.Lex`: Lexicographic order on `α × β`.

## TODO

Upgrade `Equiv.sigma_congr_left`, `Equiv.sigma_congr`, `Equiv.sigma_assoc`,
`Equiv.sigma_prod_of_equiv`, `Equiv.sigma_equiv_prod`, ... to order isomorphisms.
-/

namespace Sigma

variable {ι : Type*} {α : ι → Type*}

/-! ### Disjoint sum of orders on `Sigma` -/

protected inductive LE [∀ i, LE (α i)] : ∀ _a _b : Σ i, α i, Prop
  | fiber (i : ι) (a b : α i) : a ≤ b → Sigma.LE ⟨i, a⟩ ⟨i, b⟩

protected inductive LT [∀ i, LT (α i)] : ∀ _a _b : Σ i, α i, Prop
  | fiber (i : ι) (a b : α i) : a < b → Sigma.LT ⟨i, a⟩ ⟨i, b⟩

-- INSTANCE (free from Core): [∀

-- INSTANCE (free from Core): [∀
