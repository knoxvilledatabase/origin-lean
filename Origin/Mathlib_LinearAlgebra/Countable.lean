/-
Extracted from LinearAlgebra/Countable.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Countable modules
-/

noncomputable section

namespace Finsupp

variable {M : Type*} {R : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

-- INSTANCE (free from Core): {ι

theorem Countable.of_moduleFinite [Countable R] [Module.Finite R M] : Countable M := by
  obtain ⟨n, s, h⟩ := Module.Finite.exists_fin (R := R) (M := M)
  rw [← Set.countable_univ_iff]
  have : Countable (Submodule.span R (Set.range s)) := inferInstance
  rwa [h] at this

theorem Uncountable.of_moduleFinite [hM : Uncountable M] [Module.Finite R M] : Uncountable R := by
  by_contra!
  exact (uncountable_iff_not_countable _).mp hM <| Countable.of_moduleFinite (R := R)

end Finsupp
