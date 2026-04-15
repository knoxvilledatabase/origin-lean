/-
Extracted from Topology/Algebra/Field.lean
Genuine: 11 of 16 | Dissolved: 5 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Algebra.GroupWithZero.Divisibility
import Mathlib.Algebra.Order.Group.Pointwise.Interval
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Order.LocalExtr

/-!
# Topological fields

A topological division ring is a topological ring whose inversion function is continuous at every
non-zero element.

-/

variable {K : Type*} [DivisionRing K] [TopologicalSpace K]

-- DISSOLVED: Filter.tendsto_cocompact_mul_left₀

-- DISSOLVED: Filter.tendsto_cocompact_mul_right₀

variable (K)

class TopologicalDivisionRing extends TopologicalRing K, HasContinuousInv₀ K : Prop

section Subfield

variable {α : Type*} [Field α] [TopologicalSpace α] [TopologicalDivisionRing α]

def Subfield.topologicalClosure (K : Subfield α) : Subfield α :=
  { K.toSubring.topologicalClosure with
    carrier := _root_.closure (K : Set α)
    inv_mem' := fun x hx => by
      dsimp only at hx ⊢
      rcases eq_or_ne x 0 with (rfl | h)
      · rwa [inv_zero]
      · -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11215): TODO: Lean fails to find InvMemClass instance
        rw [← @inv_coe_set α (Subfield α) _ _ SubfieldClass.toInvMemClass K, ← Set.image_inv_eq_inv]
        exact mem_closure_image (continuousAt_inv₀ h) hx }

theorem Subfield.le_topologicalClosure (s : Subfield α) : s ≤ s.topologicalClosure :=
  _root_.subset_closure

theorem Subfield.isClosed_topologicalClosure (s : Subfield α) :
    IsClosed (s.topologicalClosure : Set α) :=
  isClosed_closure

theorem Subfield.topologicalClosure_minimal (s : Subfield α) {t : Subfield α} (h : s ≤ t)
    (ht : IsClosed (t : Set α)) : s.topologicalClosure ≤ t :=
  closure_minimal h ht

end Subfield

section affineHomeomorph

/-!
This section is about affine homeomorphisms from a topological field `𝕜` to itself.
Technically it does not require `𝕜` to be a topological field, a topological ring that
happens to be a field is enough.
-/

variable {𝕜 : Type*} [Field 𝕜] [TopologicalSpace 𝕜] [TopologicalRing 𝕜]

-- DISSOLVED: affineHomeomorph

theorem affineHomeomorph_image_Icc {𝕜 : Type*} [LinearOrderedField 𝕜] [TopologicalSpace 𝕜]
    [TopologicalRing 𝕜] (a b c d : 𝕜) (h : 0 < a) :
    affineHomeomorph a b h.ne' '' Set.Icc c d = Set.Icc (a * c + b) (a * d + b) := by
  simp [h]

theorem affineHomeomorph_image_Ico {𝕜 : Type*} [LinearOrderedField 𝕜] [TopologicalSpace 𝕜]
    [TopologicalRing 𝕜] (a b c d : 𝕜) (h : 0 < a) :
    affineHomeomorph a b h.ne' '' Set.Ico c d = Set.Ico (a * c + b) (a * d + b) := by
  simp [h]

theorem affineHomeomorph_image_Ioc {𝕜 : Type*} [LinearOrderedField 𝕜] [TopologicalSpace 𝕜]
    [TopologicalRing 𝕜] (a b c d : 𝕜) (h : 0 < a) :
    affineHomeomorph a b h.ne' '' Set.Ioc c d = Set.Ioc (a * c + b) (a * d + b) := by
  simp [h]

theorem affineHomeomorph_image_Ioo {𝕜 : Type*} [LinearOrderedField 𝕜] [TopologicalSpace 𝕜]
    [TopologicalRing 𝕜] (a b c d : 𝕜) (h : 0 < a) :
    affineHomeomorph a b h.ne' '' Set.Ioo c d = Set.Ioo (a * c + b) (a * d + b) := by
  simp [h]

end affineHomeomorph

section LocalExtr

variable {α β : Type*} [TopologicalSpace α] [LinearOrderedSemifield β] {a : α}

open Topology

theorem IsLocalMin.inv {f : α → β} {a : α} (h1 : IsLocalMin f a) (h2 : ∀ᶠ z in 𝓝 a, 0 < f z) :
    IsLocalMax f⁻¹ a := by
  filter_upwards [h1, h2] with z h3 h4 using(inv_le_inv₀ h4 h2.self_of_nhds).mpr h3

end LocalExtr

section Preconnected

/-! Some results about functions on preconnected sets valued in a ring or field with a topology. -/

open Set

variable {α 𝕜 : Type*} {f g : α → 𝕜} {S : Set α} [TopologicalSpace α] [TopologicalSpace 𝕜]
  [T1Space 𝕜]

theorem IsPreconnected.eq_one_or_eq_neg_one_of_sq_eq [Ring 𝕜] [NoZeroDivisors 𝕜]
    (hS : IsPreconnected S) (hf : ContinuousOn f S) (hsq : EqOn (f ^ 2) 1 S) :
    EqOn f 1 S ∨ EqOn f (-1) S := by
  have : DiscreteTopology ({1, -1} : Set 𝕜) := Finite.instDiscreteTopology
  have hmaps : MapsTo f S {1, -1} := by
    simpa only [EqOn, Pi.one_apply, Pi.pow_apply, sq_eq_one_iff] using hsq
  simpa using hS.eqOn_const_of_mapsTo hf hmaps

-- DISSOLVED: IsPreconnected.eq_or_eq_neg_of_sq_eq

-- DISSOLVED: IsPreconnected.eq_of_sq_eq

end Preconnected
