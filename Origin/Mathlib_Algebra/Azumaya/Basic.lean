/-
Extracted from Algebra/Azumaya/Basic.lean
Genuine: 4 of 7 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Basic properties of Azumaya algebras

In this file we prove basic facts about Azumaya algebras such as `R` is an Azumaya algebra
over itself where `R` is a commutative ring.

## Main Results

- `IsAzumaya.id`: `R` is an Azumaya algebra over itself.

- `IsAzumaya.ofAlgEquiv`: If `A` is an Azumaya algebra over `R` and `A` is isomorphic to `B`
  as an `R`-algebra, then `B` is an Azumaya algebra over `R`.

## Tags
Noncommutative algebra, Azumaya algebra, Brauer Group

-/

open scoped TensorProduct

open MulOpposite

namespace IsAzumaya

variable (R A B : Type*) [CommSemiring R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]

abbrev tensorEquivEnd : R ⊗[R] Rᵐᵒᵖ ≃ₐ[R] Module.End R R :=
  Algebra.TensorProduct.lid R Rᵐᵒᵖ |>.trans <| .moduleEndSelf R

lemma coe_tensorEquivEnd : tensorEquivEnd R = AlgHom.mulLeftRight R R := by
  ext; simp

-- INSTANCE (free from Core): id

lemma mulLeftRight_comp_congr (e : A ≃ₐ[R] B) :
    (AlgHom.mulLeftRight R B).comp (Algebra.TensorProduct.congr e e.op).toAlgHom =
    (e.toLinearEquiv.conjAlgEquiv R).toAlgHom.comp (AlgHom.mulLeftRight R A) := by
  ext <;> simp

theorem of_AlgEquiv (e : A ≃ₐ[R] B) [IsAzumaya R A] : IsAzumaya R B :=
  let _ : Module.Projective R B := .of_equiv e.toLinearEquiv
  let _ : FaithfulSMul R B := .of_injective e e.injective
  let _ : Module.Finite R B := .equiv e.toLinearEquiv
  ⟨Function.Bijective.of_comp_iff (AlgHom.mulLeftRight R B)
    (Algebra.TensorProduct.congr e e.op).bijective |>.1 <| by
    rw [← AlgEquiv.coe_algHom, ← AlgHom.coe_comp, mulLeftRight_comp_congr]
    simp [AlgHom.mulLeftRight_bij]⟩

end IsAzumaya

-- INSTANCE (free from Core): Algebra.IsCentral.instIsAzumaya
