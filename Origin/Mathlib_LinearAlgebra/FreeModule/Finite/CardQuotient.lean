/-
Extracted from LinearAlgebra/FreeModule/Finite/CardQuotient.lean
Genuine: 4 of 5 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-! # Cardinal of quotient of free finite `ℤ`-modules by submodules of full rank

## Main results

* `Submodule.natAbs_det_basis_change`: let `b` be a `ℤ`-basis for a module `M` over `ℤ` and
  let `bN` be a basis for a submodule `N` of the same dimension. Then the cardinal of `M ⧸ N`
  is given by taking the determinant of `bN` over `b`.

-/

open Module Submodule

section Submodule

variable {M : Type*} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]

theorem Submodule.natAbs_det_basis_change {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ M)
    (N : Submodule ℤ M) (bN : Basis ι ℤ N) :
    (b.det ((↑) ∘ bN)).natAbs = Nat.card (M ⧸ N) := by
  let e := b.equiv bN (Equiv.refl _)
  calc
    (b.det (N.subtype ∘ bN)).natAbs = (LinearMap.det (N.subtype ∘ₗ (e : M →ₗ[ℤ] N))).natAbs := by
      rw [Basis.det_comp_basis]
    _ = _ := natAbs_det_equiv N e

end Submodule

section AddSubgroup

theorem AddSubgroup.index_eq_natAbs_det {E : Type*} [AddCommGroup E] {ι : Type*}
    [DecidableEq ι] [Fintype ι] (bE : Basis ι ℤ E) (N : AddSubgroup E) (bN : Basis ι ℤ N) :
    N.index = (bE.det (bN ·)).natAbs :=
  have : Module.Free ℤ E := Module.Free.of_basis bE
  have : Module.Finite ℤ E := Module.Finite.of_basis bE
  (Submodule.natAbs_det_basis_change bE N.toIntSubmodule bN).symm

set_option backward.isDefEq.respectTransparency false in

theorem AddSubgroup.relIndex_eq_natAbs_det {E : Type*} [AddCommGroup E]
    (L₁ L₂ : AddSubgroup E) (H : L₁ ≤ L₂) {ι : Type*} [DecidableEq ι] [Fintype ι]
    (b₁ : Basis ι ℤ L₁.toIntSubmodule) (b₂ : Basis ι ℤ L₂.toIntSubmodule) :
    L₁.relIndex L₂ = (b₂.det (fun i ↦ ⟨b₁ i, (H (SetLike.coe_mem _))⟩)).natAbs := by
  rw [relIndex, index_eq_natAbs_det b₂ _ (b₁.map (addSubgroupOfEquivOfLe H).toIntLinearEquiv.symm)]
  rfl

theorem AddSubgroup.relIndex_eq_abs_det {E : Type*} [AddCommGroup E] [Module ℚ E]
    (L₁ L₂ : AddSubgroup E) (H : L₁ ≤ L₂) {ι : Type*} [DecidableEq ι] [Fintype ι]
    (b₁ b₂ : Basis ι ℚ E) (h₁ : L₁ = .closure (Set.range b₁)) (h₂ : L₂ = .closure (Set.range b₂)) :
    L₁.relIndex L₂ = |b₂.det b₁| := by
  rw [AddSubgroup.relIndex_eq_natAbs_det L₁ L₂ H (b₁.addSubgroupOfClosure L₁ h₁)
    (b₂.addSubgroupOfClosure L₂ h₂), Nat.cast_natAbs, Int.cast_abs]
  change |algebraMap ℤ ℚ _| = _
  rw [Basis.det_apply, Basis.det_apply, RingHom.map_det]
  congr; ext
  simp [Basis.toMatrix_apply]

end AddSubgroup
