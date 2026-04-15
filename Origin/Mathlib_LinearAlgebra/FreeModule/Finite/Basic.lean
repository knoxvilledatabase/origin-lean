/-
Extracted from LinearAlgebra/FreeModule/Finite/Basic.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Finite and free modules

We provide some instances for finite and free modules.

## Main results

* `Module.Free.ChooseBasisIndex.fintype` : If a free module is finite, then any basis is finite.
* `Module.Finite.of_basis` : A free module with a basis indexed by a `Fintype` is finite.
-/

universe u v w

-- INSTANCE (free from Core): Module.Free.ChooseBasisIndex.fintype

theorem Module.Finite.of_basis {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [_root_.Finite ι] (b : Basis ι R M) : Module.Finite R M := by
  cases nonempty_fintype ι
  classical
    refine ⟨⟨Finset.univ.image b, ?_⟩⟩
    simp only [Set.image_univ, Finset.coe_univ, Finset.coe_image, Basis.span_eq]

-- INSTANCE (free from Core): Module.Finite.matrix

example {ι₁ ι₂ R : Type*} [Semiring R] [Finite ι₁] [Finite ι₂] :

    Module.Finite R (Matrix ι₁ ι₂ R) := inferInstance
