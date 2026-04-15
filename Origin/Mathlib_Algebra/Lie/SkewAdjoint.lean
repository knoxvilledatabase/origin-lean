/-
Extracted from Algebra/Lie/SkewAdjoint.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Lie algebras of skew-adjoint endomorphisms of a bilinear form

When a module carries a bilinear form, the Lie algebra of endomorphisms of the module contains a
distinguished Lie subalgebra: the skew-adjoint endomorphisms. Such subalgebras are important
because they provide a simple, explicit construction of the so-called classical Lie algebras.

This file defines the Lie subalgebra of skew-adjoint endomorphisms cut out by a bilinear form on
a module and proves some basic related results. It also provides the corresponding definitions and
results for the Lie algebra of square matrices.

## Main definitions

  * `skewAdjointLieSubalgebra`
  * `skewAdjointLieSubalgebraEquiv`
  * `skewAdjointMatricesLieSubalgebra`
  * `skewAdjointMatricesLieSubalgebraEquiv`

## Tags

lie algebra, skew-adjoint, bilinear form
-/

universe u v w w₁

section SkewAdjointEndomorphisms

open LinearMap (BilinForm)

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

variable (B : BilinForm R M)

theorem LinearMap.BilinForm.isSkewAdjoint_bracket {f g : Module.End R M}
    (hf : f ∈ B.skewAdjointSubmodule) (hg : g ∈ B.skewAdjointSubmodule) :
    ⁅f, g⁆ ∈ B.skewAdjointSubmodule := by
  rw [mem_skewAdjointSubmodule] at *
  have hfg : IsAdjointPair B B (f * g) (g * f) := by rw [← neg_mul_neg g f]; exact hg.comp hf
  have hgf : IsAdjointPair B B (g * f) (f * g) := by rw [← neg_mul_neg f g]; exact hf.comp hg
  change IsAdjointPair B B (f * g - g * f) (-(f * g - g * f)); rw [neg_sub]
  exact hfg.sub hgf

def skewAdjointLieSubalgebra : LieSubalgebra R (Module.End R M) :=
  { B.skewAdjointSubmodule with
    lie_mem' := B.isSkewAdjoint_bracket }

variable {N : Type w} [AddCommGroup N] [Module R N] (e : N ≃ₗ[R] M)

def skewAdjointLieSubalgebraEquiv :
    skewAdjointLieSubalgebra (B.compl₁₂ (e : N →ₗ[R] M) e) ≃ₗ⁅R⁆ skewAdjointLieSubalgebra B := by
  apply LieEquiv.ofSubalgebras _ _ e.lieConj
  ext f
  simp only [Submodule.mem_map_equiv, LieSubalgebra.mem_map_submodule]
  exact (LinearMap.isPairSelfAdjoint_equiv (B := -B) (F := B) e f).symm
