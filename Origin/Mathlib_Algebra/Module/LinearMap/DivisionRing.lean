/-
Extracted from Algebra/Module/LinearMap/DivisionRing.lean
Genuine: 1 of 3 | Dissolved: 2 | Infrastructure: 0
-/
import Origin.Core

/-!
# Some lemmas about linear functionals on division rings

This file proves some results on linear functionals on division semirings.

## Main results

* `LinearMap.surjective_iff_ne_zero`: a linear functional `f` is surjective iff `f ≠ 0`.
* `LinearMap.range_smulRight_apply`: for a nonzero linear functional `f` and element `x`,
  the range of `f.smulRight x` is the span of the set `{x}`.
-/

namespace LinearMap

variable {R M M₁ : Type*} [AddCommMonoid M] [AddCommMonoid M₁]

-- DISSOLVED: surjective_iff_ne_zero

protected alias ⟨_, surjective⟩ := surjective_iff_ne_zero

theorem range_smulRight_apply_of_surjective [Semiring R] [Module R M] [Module R M₁]
    {f : M →ₗ[R] R} (hf : Function.Surjective f) (x : M₁) :
    range (f.smulRight x) = Submodule.span R {x} := Submodule.ext fun z ↦ by
  simp_rw [mem_range, smulRight_apply, Submodule.mem_span_singleton]
  refine ⟨fun ⟨w, hw⟩ ↦ ⟨f w, hw ▸ rfl⟩, fun ⟨w, hw⟩ ↦ ?_⟩
  obtain ⟨y, rfl⟩ := hf w
  exact ⟨y, hw⟩

-- DISSOLVED: range_smulRight_apply

end LinearMap
