/-
Extracted from Algebra/Order/Ring/Finset.lean
Genuine: 3 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Algebra.Order.Field.Canonical.Defs
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Nat.Cast.Order.Ring

noncomputable section

/-!
# `Finset.sup` of `Nat.cast`
-/

open Finset

namespace Nat

variable {ι R : Type*}

section LinearOrderedSemiring

variable [LinearOrderedSemiring R] {s : Finset ι}

set_option linter.docPrime false in
@[simp, norm_cast]

lemma cast_finsetSup' (f : ι → ℕ) (hs) : ((s.sup' hs f : ℕ) : R) = s.sup' hs fun i ↦ (f i : R) :=
  comp_sup'_eq_sup'_comp _ _ cast_max

set_option linter.docPrime false in
@[simp, norm_cast]

lemma cast_finsetInf' (f : ι → ℕ) (hs) : (↑(s.inf' hs f) : R) = s.inf' hs fun i ↦ (f i : R) :=
  comp_inf'_eq_inf'_comp _ _ cast_min

end LinearOrderedSemiring

@[simp, norm_cast]
lemma cast_finsetSup [CanonicallyLinearOrderedSemifield R] (s : Finset ι) (f : ι → ℕ) :
    (↑(s.sup f) : R) = s.sup fun i ↦ (f i : R) :=
  comp_sup_eq_sup_comp _ cast_max (by simp)

end Nat
