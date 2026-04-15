/-
Extracted from RingTheory/FiniteStability.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!

# Stability of finiteness conditions in commutative algebra

In this file we show that `Algebra.FiniteType` and `Algebra.FinitePresentation` are
stable under base change.

-/

open scoped TensorProduct

universe w₁ w₂ w₃

variable {R : Type w₁} [CommRing R]

variable {A : Type w₂} [CommRing A] [Algebra R A]

variable (B : Type w₃) [CommRing B] [Algebra R B]

namespace Algebra

namespace FiniteType

theorem baseChangeAux_surj {σ : Type*} {f : MvPolynomial σ R →ₐ[R] A} (hf : Function.Surjective f) :
    Function.Surjective (Algebra.TensorProduct.map (AlgHom.id B B) f) := by
  change Function.Surjective (TensorProduct.map (AlgHom.id R B) f)
  apply TensorProduct.map_surjective
  · exact Function.RightInverse.surjective (congrFun rfl)
  · exact hf

-- INSTANCE (free from Core): baseChange

end FiniteType

namespace FinitePresentation

-- INSTANCE (free from Core): baseChange

end FinitePresentation

end Algebra
