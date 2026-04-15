/-
Extracted from Order/Fin/Finset.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Order isomorphisms from Fin to finsets

We define order isomorphisms like `Fin.orderIsoTriple` from `Fin 3`
to the finset `{a, b, c}` when `a < b` and `b < c`.

## Future works

* Do the same for `Set` without too much duplication of code (TODO)
* Provide a definition which would take as an input an order
  isomorphism `e : Fin (n + 1) ≃o s` (with `s : Set α` (or `Finset α`)) and
  extend it to an order isomorphism `Fin (n + 2) ≃o Finset.insert i s` when `i < e 0` (TODO).

-/

namespace Fin

variable {α : Type*} [Preorder α]

noncomputable def orderIsoSingleton (a : α) :
    Fin 1 ≃o ({a} : Finset α) :=
  OrderIso.ofUnique _ _
