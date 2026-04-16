/-
Extracted from Algebra/Order/Monoid/Canonical/Basic.lean
Genuine: 2 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Data.Finset.Lattice.Fold

noncomputable section

/-!
# Extra lemmas about canonically ordered monoids
-/

namespace Finset

variable {ι α : Type*} [CanonicallyLinearOrderedAddCommMonoid α] {s : Finset ι} {f : ι → α}

@[simp] lemma sup_eq_zero : s.sup f = 0 ↔ ∀ i ∈ s, f i = 0 := by simp [← bot_eq_zero']

@[simp] lemma sup'_eq_zero (hs) : s.sup' hs f = 0 ↔ ∀ i ∈ s, f i = 0 := by simp [sup'_eq_sup]

end Finset
