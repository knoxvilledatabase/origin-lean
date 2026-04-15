/-
Extracted from LinearAlgebra/GeneralLinearGroup/AlgEquiv.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Algebra isomorphisms between endomorphisms of projective modules are inner

This file shows that given any algebra equivalence `f : End K V ≃ₐ[K] End K W`,
there exists a linear equivalence `T : V ≃ₗ[K] W` such that `f x = T ∘ₗ x ∘ₗ T.symm`.
In other words, for `V = W`, the map `MulSemiringAction.toAlgEquiv` from
`GeneralLinearGroup K V` to `End K V ≃ₐ[K] End K V` is surjective.

For the continuous versions, see `Mathlib/Analysis/Normed/Operator/ContinuousAlgEquiv.lean`.
-/

open Module LinearMap LinearEquiv

variable {K V W : Type*} [Semifield K] [AddCommMonoid V] [Module K V] [Projective K V]
  [AddCommMonoid W] [Module K W] [Projective K W]

variable (K V W) in

public theorem LinearEquiv.conjAlgEquiv_surjective :
    Function.Surjective (conjAlgEquiv K (S := K) (M₁ := V) (M₂ := W)) :=
  fun f ↦ f.eq_linearEquivConjAlgEquiv.imp fun _ h ↦ h.symm

public theorem Module.End.mulSemiringActionToAlgEquiv_conjAct_surjective :
    Function.Surjective
      (MulSemiringAction.toAlgEquiv (G := ConjAct (GeneralLinearGroup K V)) K (End K V)) := by
  intro f
  have ⟨T, hT⟩ := f.eq_linearEquivConjAlgEquiv
  exact ⟨.ofLinearEquiv T, hT.symm⟩
