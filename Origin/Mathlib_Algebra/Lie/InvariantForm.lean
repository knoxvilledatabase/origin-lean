/-
Extracted from Algebra/Lie/InvariantForm.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Lie algebras with non-degenerate invariant bilinear forms are semisimple

In this file we prove that a finite-dimensional Lie algebra over a field is semisimple
if it does not have non-trivial abelian ideals and it admits a
non-degenerate reflexive invariant bilinear form.
Here a form is *invariant* if it is invariant under the Lie bracket
in the sense that `⁅x, Φ⁆ = 0` for all `x` or equivalently, `Φ ⁅x, y⁆ z = Φ x ⁅y, z⁆`.

## Main results

* `LieAlgebra.InvariantForm.orthogonal`: given a Lie submodule `N` of a Lie module `M`,
  we define its orthogonal complement with respect to a non-degenerate invariant bilinear form `Φ`
  as the Lie ideal of elements `x` such that `Φ n x = 0` for all `n ∈ N`.
* `LieAlgebra.InvariantForm.isSemisimple_of_nondegenerate`: the main result of this file;
  a finite-dimensional Lie algebra over a field is semisimple
  if it does not have non-trivial abelian ideals and admits
  a non-degenerate invariant reflexive bilinear form.

## References

We follow the short and excellent paper [dieudonne1953].
-/

namespace LieAlgebra

namespace InvariantForm

section ring

variable {R L M : Type*}

variable [CommRing R] [LieRing L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M]

variable (Φ : LinearMap.BilinForm R M) (hΦ_nondeg : Φ.Nondegenerate)

variable (L) in

def _root_.LinearMap.BilinForm.lieInvariant : Prop :=
  ∀ (x : L) (y z : M), Φ ⁅x, y⁆ z = -Φ y ⁅x, z⁆

lemma _root_.LinearMap.BilinForm.lieInvariant_iff [LieAlgebra R L] [LieModule R L M] :
    Φ.lieInvariant L ↔ Φ ∈ LieModule.maxTrivSubmodule R L (LinearMap.BilinForm R M) := by
  refine ⟨fun h x ↦ ?_, fun h x y z ↦ ?_⟩
  · ext y z
    rw [LieHom.lie_apply, LinearMap.sub_apply, Module.Dual.lie_apply, LinearMap.zero_apply,
      LinearMap.zero_apply, h, sub_self]
  · replace h := LinearMap.congr_fun₂ (h x) y z
    simp only [LieHom.lie_apply, LinearMap.sub_apply, Module.Dual.lie_apply,
      LinearMap.zero_apply, sub_eq_zero] at h
    simp [← h]
