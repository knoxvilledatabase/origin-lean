/-
Extracted from Algebra/CharP/LinearMaps.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.Algebra.CharP.Algebra

/-!
# Characteristic of the ring of linear Maps

This file contains properties of the characteristic of the ring of linear maps.
The characteristic of the ring of linear maps is determined by its base ring.

## Main Results

- `CharP_if` : For a commutative semiring `R` and a `R`-module `M`,
  the characteristic of `R` is equal to the characteristic of the `R`-linear
  endomorphisms of `M` when `M` contains an element `x` such that
  `r • x = 0` implies `r = 0`.

## Notations

- `R` is a commutative semiring
- `M` is a `R`-module

## Implementation Notes

One can also deduce similar result via `charP_of_injective_ringHom` and
  `R → (M →ₗ[R] M) : r ↦ (fun (x : M) ↦ r • x)`. But this will require stronger condition
  compared to `CharP_if`.

-/

namespace Module

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

theorem charP_end {p : ℕ} [hchar : CharP R p]
    (hreduction : ∃ x : M, ∀ r : R, r • x = 0 → r = 0) : CharP (M →ₗ[R] M) p where
  cast_eq_zero_iff' n := by
    have exact : (n : M →ₗ[R] M) = (n : R) • 1 := by
      simp only [Nat.cast_smul_eq_nsmul, nsmul_eq_mul, mul_one]
    rw [exact, LinearMap.ext_iff, ← hchar.1]
    exact ⟨fun h ↦ Exists.casesOn hreduction fun x hx ↦ hx n (h x),
      fun h ↦ (congrArg (fun t ↦ ∀ x, t • x = 0) h).mpr fun x ↦ zero_smul R x⟩

end Module

instance {D : Type*} [DivisionRing D] {p : ℕ} [CharP D p] :
    CharP (D →ₗ[(Subring.center D)] D) p :=
  charP_of_injective_ringHom (Algebra.lmul (Subring.center D) D).toRingHom.injective p

instance {D : Type*} [DivisionRing D] {p : ℕ} [ExpChar D p] :
    ExpChar (D →ₗ[Subring.center D] D) p :=
  expChar_of_injective_ringHom (Algebra.lmul (Subring.center D) D).toRingHom.injective p
