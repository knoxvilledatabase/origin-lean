/-
Extracted from Topology/Instances/ZMultiples.lean
Genuine: 2 of 4 | Dissolved: 1 | Infrastructure: 1
-/
import Origin.Core

/-!
The subgroup "multiples of `a`" (`zmultiples a`) is a discrete subgroup of `ℝ`, i.e. its
intersection with compact sets is finite.
-/

noncomputable section

open Filter Int Metric Set TopologicalSpace Bornology

open scoped Topology Uniformity Interval

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

namespace Int

open Metric

-- INSTANCE (free from Core): {a

theorem tendsto_coe_cofinite : Tendsto ((↑) : ℤ → ℝ) cofinite (cocompact ℝ) := by
  apply (castAddHom ℝ).tendsto_coe_cofinite_of_discrete cast_injective
  rw [range_castAddHom, SetLike.isDiscrete_iff_discreteTopology]
  infer_instance

-- DISSOLVED: tendsto_zmultiplesHom_cofinite

end Int

namespace AddSubgroup

theorem tendsto_zmultiples_subtype_cofinite (a : ℝ) :
    Tendsto (zmultiples a).subtype cofinite (cocompact ℝ) := by
  refine (zmultiples a).tendsto_coe_cofinite_of_discrete ?_
  rw [SetLike.isDiscrete_iff_discreteTopology]
  infer_instance

end AddSubgroup
