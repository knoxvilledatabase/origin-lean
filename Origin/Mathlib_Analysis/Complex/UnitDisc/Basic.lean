/-
Extracted from Analysis/Complex/UnitDisc/Basic.lean
Genuine: 14 of 48 | Dissolved: 3 | Infrastructure: 31
-/
import Origin.Core
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.NormedSpace.BallAction

/-!
# Poincaré disc

In this file we define `Complex.UnitDisc` to be the unit disc in the complex plane. We also
introduce some basic operations on this disc.
-/

open Set Function Metric

noncomputable section

local notation "conj'" => starRingEnd ℂ

namespace Complex

def UnitDisc : Type :=
  ball (0 : ℂ) 1 deriving TopologicalSpace

open UnitDisc

namespace UnitDisc

instance instCommSemigroup : CommSemigroup UnitDisc := by unfold UnitDisc; infer_instance

instance instHasDistribNeg : HasDistribNeg UnitDisc := by unfold UnitDisc; infer_instance

instance instCoe : Coe UnitDisc ℂ := ⟨Subtype.val⟩

theorem coe_injective : Injective ((↑) : 𝔻 → ℂ) :=
  Subtype.coe_injective

theorem abs_lt_one (z : 𝔻) : abs (z : ℂ) < 1 :=
  mem_ball_zero_iff.1 z.2

-- DISSOLVED: abs_ne_one

theorem normSq_lt_one (z : 𝔻) : normSq z < 1 := by
  convert (Real.sqrt_lt' one_pos).1 z.abs_lt_one
  exact (one_pow 2).symm

-- DISSOLVED: coe_ne_one

theorem coe_ne_neg_one (z : 𝔻) : (z : ℂ) ≠ -1 :=
  ne_of_apply_ne abs <| by
    rw [abs.map_neg, map_one]
    exact z.abs_ne_one

-- DISSOLVED: one_add_coe_ne_zero

@[simp, norm_cast]
theorem coe_mul (z w : 𝔻) : ↑(z * w) = (z * w : ℂ) :=
  rfl

def mk (z : ℂ) (hz : abs z < 1) : 𝔻 :=
  ⟨z, mem_ball_zero_iff.2 hz⟩

@[simp]
theorem coe_mk (z : ℂ) (hz : abs z < 1) : (mk z hz : ℂ) = z :=
  rfl

@[simp]
theorem mk_coe (z : 𝔻) (hz : abs (z : ℂ) < 1 := z.abs_lt_one) : mk z hz = z :=
  Subtype.eta _ _

@[simp]
theorem mk_neg (z : ℂ) (hz : abs (-z) < 1) : mk (-z) hz = -mk z (abs.map_neg z ▸ hz) :=
  rfl

instance : SemigroupWithZero 𝔻 :=
  { instCommSemigroup with
    zero := mk 0 <| (map_zero _).trans_lt one_pos
    zero_mul := fun _ => coe_injective <| zero_mul _
    mul_zero := fun _ => coe_injective <| mul_zero _ }

@[simp]
theorem coe_zero : ((0 : 𝔻) : ℂ) = 0 :=
  rfl

@[simp]
theorem coe_eq_zero {z : 𝔻} : (z : ℂ) = 0 ↔ z = 0 :=
  coe_injective.eq_iff' coe_zero

instance : Inhabited 𝔻 :=
  ⟨0⟩

instance circleAction : MulAction Circle 𝔻 :=
  mulActionSphereBall

instance isScalarTower_circle_circle : IsScalarTower Circle Circle 𝔻 :=
  isScalarTower_sphere_sphere_ball

instance isScalarTower_circle : IsScalarTower Circle 𝔻 𝔻 :=
  isScalarTower_sphere_ball_ball

instance instSMulCommClass_circle : SMulCommClass Circle 𝔻 𝔻 :=
  instSMulCommClass_sphere_ball_ball

instance instSMulCommClass_circle' : SMulCommClass 𝔻 Circle 𝔻 :=
  SMulCommClass.symm _ _ _

@[simp, norm_cast]
theorem coe_smul_circle (z : Circle) (w : 𝔻) : ↑(z • w) = (z * w : ℂ) :=
  rfl

instance closedBallAction : MulAction (closedBall (0 : ℂ) 1) 𝔻 :=
  mulActionClosedBallBall

instance isScalarTower_closedBall_closedBall :
    IsScalarTower (closedBall (0 : ℂ) 1) (closedBall (0 : ℂ) 1) 𝔻 :=
  isScalarTower_closedBall_closedBall_ball

instance isScalarTower_closedBall : IsScalarTower (closedBall (0 : ℂ) 1) 𝔻 𝔻 :=
  isScalarTower_closedBall_ball_ball

instance instSMulCommClass_closedBall : SMulCommClass (closedBall (0 : ℂ) 1) 𝔻 𝔻 :=
  ⟨fun _ _ _ => Subtype.ext <| mul_left_comm _ _ _⟩

instance instSMulCommClass_closedBall' : SMulCommClass 𝔻 (closedBall (0 : ℂ) 1) 𝔻 :=
  SMulCommClass.symm _ _ _

instance instSMulCommClass_circle_closedBall : SMulCommClass Circle (closedBall (0 : ℂ) 1) 𝔻 :=
  instSMulCommClass_sphere_closedBall_ball

instance instSMulCommClass_closedBall_circle : SMulCommClass (closedBall (0 : ℂ) 1) Circle 𝔻 :=
  SMulCommClass.symm _ _ _

@[simp, norm_cast]
theorem coe_smul_closedBall (z : closedBall (0 : ℂ) 1) (w : 𝔻) : ↑(z • w) = (z * w : ℂ) :=
  rfl

def re (z : 𝔻) : ℝ :=
  Complex.re z

def im (z : 𝔻) : ℝ :=
  Complex.im z

@[simp, norm_cast]
theorem re_coe (z : 𝔻) : (z : ℂ).re = z.re :=
  rfl

@[simp, norm_cast]
theorem im_coe (z : 𝔻) : (z : ℂ).im = z.im :=
  rfl

@[simp]
theorem re_neg (z : 𝔻) : (-z).re = -z.re :=
  rfl

@[simp]
theorem im_neg (z : 𝔻) : (-z).im = -z.im :=
  rfl

def conj (z : 𝔻) : 𝔻 :=
  mk (conj' ↑z) <| (abs_conj z).symm ▸ z.abs_lt_one

@[simp]
theorem coe_conj (z : 𝔻) : (z.conj : ℂ) = conj' ↑z :=
  rfl

@[simp]
theorem conj_zero : conj 0 = 0 :=
  coe_injective (map_zero conj')

@[simp]
theorem conj_conj (z : 𝔻) : conj (conj z) = z :=
  coe_injective <| Complex.conj_conj (z : ℂ)

@[simp]
theorem conj_neg (z : 𝔻) : (-z).conj = -z.conj :=
  rfl

@[simp]
theorem re_conj (z : 𝔻) : z.conj.re = z.re :=
  rfl

@[simp]
theorem im_conj (z : 𝔻) : z.conj.im = -z.im :=
  rfl

@[simp]
theorem conj_mul (z w : 𝔻) : (z * w).conj = z.conj * w.conj :=
  Subtype.ext <| map_mul _ _ _

end UnitDisc

end Complex
