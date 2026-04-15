/-
Extracted from RingTheory/QuotSMulTop.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Reducing a module modulo an element of the ring

Given a commutative ring `R` and an element `r : R`, the association
`M ↦ M ⧸ rM` extends to a functor on the category of `R`-modules. This functor
is isomorphic to the functor of tensoring by `R ⧸ (r)` on either side, but can
be more convenient to work with since we can work with quotient types instead
of fiddling with simple tensors.

## Tags

module, commutative algebra
-/

open scoped Pointwise

variable {R} [CommRing R] (r : R) (M : Type*) {M' M''}
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    [AddCommGroup M''] [Module R M'']

abbrev QuotSMulTop := M ⧸ r • (⊤ : Submodule R M)

namespace QuotSMulTop

open Submodule Function TensorProduct

protected def congr (e : M' ≃ₗ[R] M'') : QuotSMulTop r M' ≃ₗ[R] QuotSMulTop r M'' :=
  Submodule.Quotient.equiv (r • ⊤) (r • ⊤) e <|
    (Submodule.map_pointwise_smul r _ e.toLinearMap).trans (by simp)

noncomputable def equivQuotTensor :
    QuotSMulTop r M ≃ₗ[R] (R ⧸ Ideal.span {r}) ⊗[R] M :=
  quotEquivOfEq _ _ (ideal_span_singleton_smul _ _).symm ≪≫ₗ
    (quotTensorEquivQuotSMul M _).symm

noncomputable def equivTensorQuot :
    QuotSMulTop r M ≃ₗ[R] M ⊗[R] (R ⧸ Ideal.span {r}) :=
  quotEquivOfEq _ _ (ideal_span_singleton_smul _ _).symm ≪≫ₗ
    (tensorQuotEquivQuotSMul M _).symm

variable {M}

def map : (M →ₗ[R] M') →ₗ[R] QuotSMulTop r M →ₗ[R] QuotSMulTop r M' :=
  Submodule.mapQLinear _ _ ∘ₗ LinearMap.id.codRestrict _ fun _ =>
    map_le_iff_le_comap.mp <| le_of_eq_of_le (map_pointwise_smul _ _ _) <|
      smul_mono_right r le_top
