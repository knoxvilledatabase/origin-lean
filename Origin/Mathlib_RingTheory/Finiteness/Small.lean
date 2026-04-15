/-
Extracted from RingTheory/Finiteness/Small.lean
Genuine: 5 of 11 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core

/-! # Smallness properties of modules and algebras -/

universe u

namespace Submodule

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

-- INSTANCE (free from Core): small_sup

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): small_iSup

theorem FG.small [Small.{u} R] (P : Submodule R M) (hP : P.FG) : Small.{u} P := by
  rw [fg_iff_exists_fin_generating_family] at hP
  obtain ⟨n, s, rfl⟩ := hP
  rw [← Fintype.range_linearCombination]
  apply small_range

variable (R M) in

theorem _root_.Module.Finite.small [Small.{u} R] [Module.Finite R M] : Small.{u} M := by
  have : Small.{u} (⊤ : Submodule R M) :=
    FG.small _ (Module.finite_def.mp inferInstance)
  rwa [← small_univ_iff]

-- INSTANCE (free from Core): small_span_singleton

theorem small_span [Small.{u} R] (s : Set M) [Small.{u} s] :
    Small.{u} (span R s) := by
  suffices span R s = iSup (fun i : s ↦ span R ({(↑i : M)} : Set M)) by
    rw [this]
    apply small_iSup
  simp [← Submodule.span_iUnion]

end Submodule

variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]

namespace Algebra

open MvPolynomial AlgHom

-- INSTANCE (free from Core): small_adjoin

theorem _root_.Subalgebra.FG.small [Small.{u} R] {A : Subalgebra R S} (fgS : A.FG) :
    Small.{u} A := by
  obtain ⟨s, hs, rfl⟩ := fgS
  exact small_adjoin

theorem FiniteType.small [Small.{u} R] [Algebra.FiniteType R S] :
    Small.{u} S := by
  have : Small.{u} (⊤ : Subalgebra R S) :=
    Subalgebra.FG.small Algebra.FiniteType.out
  rwa [← small_univ_iff]

end Algebra
