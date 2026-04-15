/-
Extracted from Order/PrimeIdeal.lean
Genuine: 7 of 7 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Prime ideals

## Main definitions

Throughout this file, `P` is at least a preorder, but some sections require more
structure, such as a bottom element, a top element, or a join-semilattice structure.

- `Order.Ideal.PrimePair`: A pair of an `Order.Ideal` and an `Order.PFilter` which form a partition
  of `P`.  This is useful as giving the data of a prime ideal is the same as giving the data of a
  prime filter.
- `Order.Ideal.IsPrime`: a predicate for prime ideals. Dual to the notion of a prime filter.
- `Order.PFilter.IsPrime`: a predicate for prime filters. Dual to the notion of a prime ideal.

## References

- <https://en.wikipedia.org/wiki/Ideal_(order_theory)>

## Tags

ideal, prime

-/

open Order.PFilter

namespace Order

variable {P : Type*}

namespace Ideal

structure PrimePair (P : Type*) [Preorder P] where
  I : Ideal P
  F : PFilter P
  isCompl_I_F : IsCompl (I : Set P) F

namespace PrimePair

variable [Preorder P] (IF : PrimePair P)

theorem compl_I_eq_F : (IF.I : Set P)ᶜ = IF.F :=
  IF.isCompl_I_F.compl_eq

theorem compl_F_eq_I : (IF.F : Set P)ᶜ = IF.I :=
  IF.isCompl_I_F.eq_compl.symm

theorem I_isProper : IsProper IF.I := by
  obtain ⟨w, h⟩ := IF.F.nonempty
  apply isProper_of_notMem (_ : w ∉ IF.I)
  rwa [← IF.compl_I_eq_F] at h

protected theorem disjoint : Disjoint (IF.I : Set P) IF.F :=
  IF.isCompl_I_F.disjoint

theorem I_union_F : (IF.I : Set P) ∪ IF.F = Set.univ :=
  IF.isCompl_I_F.sup_eq_top

theorem F_union_I : (IF.F : Set P) ∪ IF.I = Set.univ :=
  IF.isCompl_I_F.symm.sup_eq_top

end PrimePair
