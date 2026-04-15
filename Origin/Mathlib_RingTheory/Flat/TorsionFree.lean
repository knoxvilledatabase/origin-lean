/-
Extracted from RingTheory/Flat/TorsionFree.lean
Genuine: 3 of 4 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Relationships between flatness and torsionfreeness.

We show that flat implies torsion-free, and that they're the same
concept for rings satisfying a certain property, including Dedekind
domains and valuation rings.

## Main theorems

* `Module.Flat.isSMulRegular_of_nonZeroDivisors`: Scalar multiplication by a nonzerodivisor of `R`
  is injective on a flat `R`-module.
* `Module.Flat.torsion_eq_bot`: `Torsion R M = ⊥` if `M` is a flat `R`-module.
* `Module.Flat.flat_iff_torsion_eq_bot_of_valuationRing_localized_maximal`: if localizing `R` at
  the complement of any maximal ideal is a valuation ring then `Torsion R M = ⊥` iff `M` is a
  flat `R`-module.
-/

open Function (Injective Surjective)

open LinearMap (lsmul rTensor lTensor)

open Submodule (IsPrincipal torsion)

open TensorProduct

namespace Module.Flat

section Semiring

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

open LinearMap in

lemma isSMulRegular_of_isRegular {r : R} (hr : IsRegular r) [Flat R M] :
    IsSMulRegular M r := by
  -- `r ∈ R⁰` implies that `toSpanSingleton R R r`, i.e. `(r * ⬝) : R → R` is injective
  -- Flatness implies that corresponding map `R ⊗[R] M →ₗ[R] R ⊗[R] M` is injective
  have h := Flat.rTensor_preserves_injective_linearMap (M := M)
    (toSpanSingleton R R r) <| hr.right
  -- But precomposing and postcomposing with the isomorphism `M ≃ₗ[R] (R ⊗[R] M)`
  -- we get a map `M →ₗ[R] M` which is just `(r • ·)`.
  have h2 : (fun (x : M) ↦ r • x) = ((TensorProduct.lid R M) ∘ₗ
            (rTensor M (toSpanSingleton R R r)) ∘ₗ
            (TensorProduct.lid R M).symm) := by ext; simp
  -- Hence `(r • ·) : M → M` is also injective
  rw [IsSMulRegular, h2]
  simp [h, LinearEquiv.injective]

-- INSTANCE (free from Core): isTorsionFree

end Semiring

section Ring

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

open scoped nonZeroDivisors

open LinearMap in

lemma isSMulRegular_of_nonZeroDivisors {r : R} (hr : r ∈ R⁰) [Flat R M] : IsSMulRegular M r := by
  apply isSMulRegular_of_isRegular
  exact le_nonZeroDivisors_iff_isRegular.mp (le_refl R⁰) ⟨r, hr⟩

theorem torsion_eq_bot [Flat R M] : torsion R M = ⊥ := by
  rw [eq_bot_iff]
  -- indeed the definition of torsion means "annihilated by a nonzerodivisor"
  rintro m ⟨⟨r, hr⟩, h⟩
  -- and we just showed that 0 is the only element with this property
  exact isSMulRegular_of_nonZeroDivisors hr (by simpa using h)
