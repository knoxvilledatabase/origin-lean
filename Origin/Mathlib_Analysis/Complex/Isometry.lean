/-
Extracted from Analysis/Complex/Isometry.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Isometries of the Complex Plane

The lemma `linear_isometry_complex` states the classification of isometries in the complex plane.
Specifically, isometries with rotations but without translation.
The proof involves:
1. creating a linear isometry `g` with two fixed points, `g(0) = 0`, `g(1) = 1`
2. applying `linear_isometry_complex_aux` to `g`

The proof of `linear_isometry_complex_aux` is separated in the following parts:
1. show that the real parts match up: `LinearIsometry.re_apply_eq_re`
2. show that I maps to either I or -I
3. every z is a linear combination of a + b * I

## References

* [Isometries of the Complex Plane](http://helmut.knaust.info/mediawiki/images/b/b5/Iso.pdf)
-/

noncomputable section

suppress_compilation -- needed to avoid a panic!

open Complex

open CharZero

open ComplexConjugate

local notation "|" x "|" => Complex.abs x

set_option backward.isDefEq.respectTransparency false in

def rotation : Circle →* ℂ ≃ₗᵢ[ℝ] ℂ where
  toFun a :=
    { DistribMulAction.toLinearEquiv ℝ ℂ a with
      norm_map' x := show ‖a * x‖ = ‖x‖ by
        rw [norm_mul, Circle.norm_coe, one_mul] }
  map_one' := LinearIsometryEquiv.ext <| by simp
  map_mul' a b := LinearIsometryEquiv.ext <| mul_smul a b
