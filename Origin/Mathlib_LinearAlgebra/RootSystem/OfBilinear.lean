/-
Extracted from LinearAlgebra/RootSystem/OfBilinear.lean
Genuine: 2 of 3 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core

/-!
# Root pairings made from bilinear forms
A common construction of root systems is given by taking the set of all vectors in an integral
lattice for which reflection yields an automorphism of the lattice.  In this file, we generalize
this construction, replacing the ring of integers with an arbitrary commutative ring and the
integral lattice with an arbitrary reflexive module equipped with a bilinear form.

## Main definitions:
* `LinearMap.IsReflective`: Length is a regular value of `R`, and reflection is definable.
* `LinearMap.IsReflective.coroot`: The coroot corresponding to a reflective vector.
* `RootPairing.of_Bilinear`: The root pairing whose roots are reflective vectors.

## TODO
* properties
-/

open Set Function Module

noncomputable section

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

namespace LinearMap

structure IsReflective (B : M →ₗ[R] M →ₗ[R] R) (x : M) : Prop where
  regular : IsRegular (B x x)
  dvd_two_mul : ∀ y, B x x ∣ 2 * B x y

variable (B : M →ₗ[R] M →ₗ[R] R) {x : M}

namespace IsReflective

-- DISSOLVED: of_dvd_two

variable (hx : IsReflective B x)

def coroot : M →ₗ[R] R where
  toFun y := (hx.2 y).choose
  map_add' a b := by
    refine hx.1.1 ?_
    simp only
    rw [← (hx.2 (a + b)).choose_spec, mul_add, ← (hx.2 a).choose_spec, ← (hx.2 b).choose_spec,
      map_add, mul_add]
  map_smul' r a := by
    refine hx.1.1 ?_
    simp only [RingHom.id_apply]
    rw [← (hx.2 (r • a)).choose_spec, smul_eq_mul, mul_left_comm, ← (hx.2 a).choose_spec, map_smul,
      two_mul, smul_eq_mul, two_mul, mul_add]
