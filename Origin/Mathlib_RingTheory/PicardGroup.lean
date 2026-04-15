/-
Extracted from RingTheory/PicardGroup.lean
Genuine: 9 of 9 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The Picard group of a commutative ring

This file defines the Picard group `CommRing.Pic R` of a commutative ring `R` as the type of
invertible `R`-modules (in the sense that `M` is invertible if there exists another `R`-module
`N` such that `M ⊗[R] N ≃ₗ[R] R`) up to isomorphism, equipped with tensor product as multiplication.

## Main definition

- `Module.Invertible R M` says that the canonical map `Mᵛ ⊗[R] M → R` is an isomorphism.
  To show that `M` is invertible, it suffices to provide an arbitrary `R`-module `N`
  and an isomorphism `N ⊗[R] M ≃ₗ[R] R`, see `Module.Invertible.right`.

- `ClassGroup.equivPic`: the class group of a domain is isomorphic to the Picard group.

## Main results

- An invertible module is finite and projective (provided as instances).

- `Module.Invertible.free_iff_linearEquiv`: an invertible module is free iff it is isomorphic to
  the ring, i.e. its class is trivial in the Picard group.

- `Submodule.ker_unitsToPic`, `Submodule.range_unitsToPic`: exactness of the sequence
  `1 → Rˣ → Aˣ → (Submodule R A)ˣ → Pic R → Pic A` at the last two spots.
  See Theorem 2.4 in [RobertsSingh1993] or Exercise I.3.7(iv) and Proposition I.3.5 in [Weibel2013].

## References

- https://qchu.wordpress.com/2014/10/19/the-picard-groups/
- https://mathoverflow.net/questions/13768/what-is-the-right-definition-of-the-picard-group-of-a-commutative-ring
- https://mathoverflow.net/questions/375725/picard-group-vs-class-group
- [Weibel2013], https://sites.math.rutgers.edu/~weibel/Kbook/Kbook.I.pdf
- [Stacks: Picard groups of rings](https://stacks.math.columbia.edu/tag/0AFW)

## TODO

Show:
- Invertible modules over a commutative ring have the same cardinality as the ring.

- Establish other characterizations of invertible modules, e.g. they are modules that
  become free of rank one when localized at every prime ideal.
  See [Stacks: Finite projective modules](https://stacks.math.columbia.edu/tag/00NX).
- Connect to invertible sheaves on `Spec R`. More generally, connect projective `R`-modules of
  constant finite rank to locally free sheaves on `Spec R`.
- Exhibit isomorphism with sheaf cohomology `H¹(Spec R, 𝓞ˣ)`.
-/

open TensorProduct

universe u v

variable (R : Type u) (M : Type v) (N P Q A : Type*) [CommSemiring R]

variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q]

variable [Module R M] [Module R N] [Module R P] [Module R Q]

namespace Module

protected class Invertible : Prop where
  bijective : Function.Bijective (contractLeft R M)

namespace Invertible

noncomputable def linearEquiv [Module.Invertible R M] : Module.Dual R M ⊗[R] M ≃ₗ[R] R :=
  .ofBijective _ Invertible.bijective

variable {R M N}

section LinearEquiv

variable (e : M ⊗[R] N ≃ₗ[R] R)

noncomputable abbrev leftCancelEquiv : M ⊗[R] (N ⊗[R] P) ≃ₗ[R] P :=
  (TensorProduct.assoc R M N P).symm ≪≫ₗ e.rTensor P ≪≫ₗ TensorProduct.lid R P

noncomputable abbrev rightCancelEquiv : (P ⊗[R] M) ⊗[R] N ≃ₗ[R] P :=
  TensorProduct.assoc R P M N ≪≫ₗ e.lTensor P ≪≫ₗ TensorProduct.rid R P

variable {P Q} in

theorem leftCancelEquiv_comp_lTensor_comp_symm (f : P →ₗ[R] Q) :
    leftCancelEquiv Q e ∘ₗ (f.lTensor N).lTensor M ∘ₗ (leftCancelEquiv P e).symm = f := by
  rw [← LinearMap.comp_assoc, LinearEquiv.comp_toLinearMap_symm_eq]; ext; simp

variable {P Q} in

theorem rightCancelEquiv_comp_rTensor_comp_symm (f : P →ₗ[R] Q) :
    rightCancelEquiv Q e ∘ₗ (f.rTensor M).rTensor N ∘ₗ (rightCancelEquiv P e).symm = f := by
  rw [← LinearMap.comp_assoc, LinearEquiv.comp_toLinearMap_symm_eq]; ext; simp

noncomputable def rTensorInv : (P ⊗[R] M →ₗ[R] Q ⊗[R] M) →ₗ[R] (P →ₗ[R] Q) :=
  ((rightCancelEquiv Q e).congrRight ≪≫ₗ (rightCancelEquiv P e).congrLeft _ R) ∘ₗ
    LinearMap.rTensorHom N

theorem rTensorInv_leftInverse : Function.LeftInverse (rTensorInv P Q e) (.rTensorHom M) :=
  fun _ ↦ by
    simp_rw [rTensorInv, LinearEquiv.coe_trans, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
    rw [← LinearEquiv.eq_symm_apply]
    ext; simp [LinearEquiv.congrLeft, LinearEquiv.congrRight, LinearEquiv.arrowCongrAddEquiv]

theorem rTensorInv_injective : Function.Injective (rTensorInv P Q e) := by
  simpa [rTensorInv] using (rTensorInv_leftInverse _ _ <| TensorProduct.comm R N M ≪≫ₗ e).injective
