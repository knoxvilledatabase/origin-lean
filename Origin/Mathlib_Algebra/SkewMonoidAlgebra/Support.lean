/-
Extracted from Algebra/SkewMonoidAlgebra/Support.lean
Genuine: 4 of 5 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core

/-!
# Lemmas about the support of an element of a skew monoid algebra

For `f : SkewMonoidAlgebra k G`, `f.support` is the set of all `a ∈ G` such that `f.coeff a ≠ 0`.
-/

open scoped Pointwise

namespace SkewMonoidAlgebra

open Finset Finsupp

variable {k G : Type*}

section AddCommMonoid

variable [AddCommMonoid k] {a : G} {b : k}

-- DISSOLVED: support_single_ne_zero

theorem support_single_subset : (single a b).support ⊆ {a} := Finsupp.support_single_subset

theorem support_sum {k' G' : Type*} [DecidableEq G'] [AddCommMonoid k'] {f : SkewMonoidAlgebra k G}
    {g : G → k → SkewMonoidAlgebra k' G'} :
    (f.sum g).support ⊆ f.support.biUnion fun a ↦ (g a (f.coeff a)).support := by
  simp_rw [support, toFinsupp_sum']
  apply Finsupp.support_sum

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup k]

theorem support_neg (p : SkewMonoidAlgebra k G) : (-p).support = p.support := by
  rw [support, toFinsupp_neg, Finsupp.support_neg, support_toFinsupp]

end AddCommGroup

section AddCommMonoidWithOne

variable [One G] [AddCommMonoidWithOne k]

lemma support_one_subset : (1 : SkewMonoidAlgebra k G).support ⊆ 1 :=
  Finsupp.support_single_subset
