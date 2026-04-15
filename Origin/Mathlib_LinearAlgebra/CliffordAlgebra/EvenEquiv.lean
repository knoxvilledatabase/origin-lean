/-
Extracted from LinearAlgebra/CliffordAlgebra/EvenEquiv.lean
Genuine: 9 of 9 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Isomorphisms with the even subalgebra of a Clifford algebra

This file provides some notable isomorphisms regarding the even subalgebra, `CliffordAlgebra.even`.

## Main definitions

* `CliffordAlgebra.equivEven`: Every Clifford algebra is isomorphic as an algebra to the even
  subalgebra of a Clifford algebra with one more dimension.
  * `CliffordAlgebra.EquivEven.Q'`: The quadratic form used by this "one-up" algebra.
  * `CliffordAlgebra.toEven`: The simp-normal form of the forward direction of this isomorphism.
  * `CliffordAlgebra.ofEven`: The simp-normal form of the reverse direction of this isomorphism.

* `CliffordAlgebra.evenEquivEvenNeg`: Every even subalgebra is isomorphic to the even subalgebra
  of the Clifford algebra with negated quadratic form.
  * `CliffordAlgebra.evenToNeg`: The simp-normal form of each direction of this isomorphism.

## Main results

* `CliffordAlgebra.coe_toEven_reverse_involute`: the behavior of `CliffordAlgebra.toEven` on the
  "Clifford conjugate", that is `CliffordAlgebra.reverse` composed with
  `CliffordAlgebra.involute`.
-/

namespace CliffordAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

variable (Q : QuadraticForm R M)

/-! ### Constructions needed for `CliffordAlgebra.equivEven` -/

namespace EquivEven

abbrev Q' : QuadraticForm R (M × R) :=
  Q.prod <| -QuadraticMap.sq (R := R)

theorem Q'_apply (m : M × R) : Q' Q m = Q m.1 - m.2 * m.2 :=
  (sub_eq_add_neg _ _).symm

def e0 : CliffordAlgebra (Q' Q) :=
  ι (Q' Q) (0, 1)

def v : M →ₗ[R] CliffordAlgebra (Q' Q) :=
  ι (Q' Q) ∘ₗ LinearMap.inl _ _ _

theorem ι_eq_v_add_smul_e0 (m : M) (r : R) : ι (Q' Q) (m, r) = v Q m + r • e0 Q := by
  rw [e0, v, LinearMap.comp_apply, LinearMap.inl_apply, ← map_smul, Prod.smul_mk,
    smul_zero, smul_eq_mul, mul_one, ← map_add, Prod.mk_add_mk, zero_add, add_zero]

theorem e0_mul_e0 : e0 Q * e0 Q = -1 :=
  (ι_sq_scalar _ _).trans <| by simp

theorem v_sq_scalar (m : M) : v Q m * v Q m = algebraMap _ _ (Q m) :=
  (ι_sq_scalar _ _).trans <| by simp

theorem neg_e0_mul_v (m : M) : -(e0 Q * v Q m) = v Q m * e0 Q := by
  refine neg_eq_of_add_eq_zero_right ((ι_mul_ι_add_swap _ _).trans ?_)
  dsimp [QuadraticMap.polar]
  simp only [add_zero, mul_zero, mul_one, zero_add, neg_zero,
    add_sub_cancel_right, sub_self, map_zero]

theorem neg_v_mul_e0 (m : M) : -(v Q m * e0 Q) = e0 Q * v Q m := by
  rw [neg_eq_iff_eq_neg]
  exact (neg_e0_mul_v _ m).symm
