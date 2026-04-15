/-
Extracted from Data/Multiset/Sym.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Unordered tuples of elements of a multiset

Defines `Multiset.sym` and the specialized `Multiset.sym2` for computing multisets of all
unordered n-tuples from a given multiset. These are multiset versions of `Nat.multichoose`.

## Main declarations

* `Multiset.sym2`: `xs.sym2` is the multiset of all unordered pairs of elements from `xs`,
  with multiplicity. The multiset's values are in `Sym2 α`.

## TODO

* Once `List.Perm.sym` is defined, define
  ```lean
  protected def sym (n : Nat) (m : Multiset α) : Multiset (Sym α n) :=
    m.liftOn (fun xs => xs.sym n) (List.perm.sym n)
  ```
  and then use this to remove the `DecidableEq` assumption from `Finset.sym`.

* `theorem injective_sym2 : Function.Injective (Multiset.sym2 : Multiset α → _)`

* `theorem strictMono_sym2 : StrictMono (Multiset.sym2 : Multiset α → _)`

-/

namespace Multiset

variable {α β : Type*}

section Sym2

protected def sym2 (m : Multiset α) : Multiset (Sym2 α) :=
  m.liftOn (fun xs => xs.sym2) fun _ _ h => by rw [coe_eq_coe]; exact h.sym2
