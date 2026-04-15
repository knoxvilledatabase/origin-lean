/-
Extracted from Data/Rat/Cast/Defs.lean
Genuine: 27 | Conflates: 0 | Dissolved: 12 | Infrastructure: 6
-/
import Origin.Core
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Group.Commute.Basic
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Rat.Lemmas
import Mathlib.Order.Nat
import Mathlib.Algebra.GroupWithZero.Units.Lemmas

/-!
# Casts for Rational Numbers

## Summary

We define the canonical injection from ℚ into an arbitrary division ring and prove various
casting lemmas showing the well-behavedness of this injection.

## Tags

rat, rationals, field, ℚ, numerator, denominator, num, denom, cast, coercion, casting
-/

variable {F ι α β : Type*}

namespace NNRat

variable [DivisionSemiring α] {q r : ℚ≥0}

@[simp, norm_cast] lemma cast_natCast (n : ℕ) : ((n : ℚ≥0) : α) = n := by simp [cast_def]

@[simp, norm_cast] lemma cast_ofNat (n : ℕ) [n.AtLeastTwo] :
    no_index (OfNat.ofNat n : ℚ≥0) = (OfNat.ofNat n : α) := cast_natCast _

@[simp, norm_cast] lemma cast_zero : ((0 : ℚ≥0) : α) = 0 := (cast_natCast _).trans Nat.cast_zero

@[simp, norm_cast] lemma cast_one : ((1 : ℚ≥0) : α) = 1 := (cast_natCast _).trans Nat.cast_one

lemma cast_commute (q : ℚ≥0) (a : α) : Commute (↑q) a := by
  simpa only [cast_def] using (q.num.cast_commute a).div_left (q.den.cast_commute a)

lemma commute_cast (a : α) (q : ℚ≥0) : Commute a q := (cast_commute ..).symm

lemma cast_comm (q : ℚ≥0) (a : α) : q * a = a * q := cast_commute _ _

-- DISSOLVED: cast_divNat_of_ne_zero

-- DISSOLVED: cast_add_of_ne_zero

-- DISSOLVED: cast_mul_of_ne_zero

-- DISSOLVED: cast_inv_of_ne_zero

-- DISSOLVED: cast_div_of_ne_zero

end NNRat

namespace Rat

variable [DivisionRing α] {p q : ℚ}

@[simp, norm_cast]
theorem cast_intCast (n : ℤ) : ((n : ℚ) : α) = n :=
  (cast_def _).trans <| show (n / (1 : ℕ) : α) = n by rw [Nat.cast_one, div_one]

@[simp, norm_cast]
theorem cast_natCast (n : ℕ) : ((n : ℚ) : α) = n := by
  rw [← Int.cast_natCast, cast_intCast, Int.cast_natCast]

@[simp, norm_cast] lemma cast_ofNat (n : ℕ) [n.AtLeastTwo] :
    ((no_index (OfNat.ofNat n : ℚ)) : α) = (OfNat.ofNat n : α) := by
  simp [cast_def]

@[simp, norm_cast]
theorem cast_zero : ((0 : ℚ) : α) = 0 :=
  (cast_intCast _).trans Int.cast_zero

@[simp, norm_cast]
theorem cast_one : ((1 : ℚ) : α) = 1 :=
  (cast_intCast _).trans Int.cast_one

theorem cast_commute (r : ℚ) (a : α) : Commute (↑r) a := by
  simpa only [cast_def] using (r.1.cast_commute a).div_left (r.2.cast_commute a)

theorem cast_comm (r : ℚ) (a : α) : (r : α) * a = a * r :=
  (cast_commute r a).eq

theorem commute_cast (a : α) (r : ℚ) : Commute a r :=
  (r.cast_commute a).symm

-- DISSOLVED: cast_divInt_of_ne_zero

-- DISSOLVED: cast_mkRat_of_ne_zero

-- DISSOLVED: cast_add_of_ne_zero

@[simp, norm_cast] lemma cast_neg (q : ℚ) : ↑(-q) = (-q : α) := by simp [cast_def, neg_div]

-- DISSOLVED: cast_sub_of_ne_zero

-- DISSOLVED: cast_mul_of_ne_zero

-- DISSOLVED: cast_inv_of_ne_zero

-- DISSOLVED: cast_div_of_ne_zero

end Rat

open Rat

variable [FunLike F α β]

@[simp] lemma map_nnratCast [DivisionSemiring α] [DivisionSemiring β] [RingHomClass F α β] (f : F)
    (q : ℚ≥0) : f q = q := by simp_rw [NNRat.cast_def, map_div₀, map_natCast]

@[simp]
lemma eq_nnratCast [DivisionSemiring α] [FunLike F ℚ≥0 α] [RingHomClass F ℚ≥0 α] (f : F) (q : ℚ≥0) :
    f q = q := by rw [← map_nnratCast f, NNRat.cast_id]

@[simp]
theorem map_ratCast [DivisionRing α] [DivisionRing β] [RingHomClass F α β] (f : F) (q : ℚ) :
    f q = q := by rw [cast_def, map_div₀, map_intCast, map_natCast, cast_def]

@[simp] lemma eq_ratCast [DivisionRing α] [FunLike F ℚ α] [RingHomClass F ℚ α] (f : F) (q : ℚ) :
    f q = q := by rw [← map_ratCast f, Rat.cast_id]

namespace MonoidWithZeroHomClass

variable {M₀ : Type*} [MonoidWithZero M₀]

section NNRat

variable [FunLike F ℚ≥0 M₀] [MonoidWithZeroHomClass F ℚ≥0 M₀] {f g : F}

lemma ext_nnrat' (h : ∀ n : ℕ, f n = g n) : f = g :=
  (DFunLike.ext f g) fun r => by
    rw [← r.num_div_den, div_eq_mul_inv, map_mul, map_mul, h, eq_on_inv₀ f g]
    apply h

@[ext]
lemma ext_nnrat {f g : ℚ≥0 →*₀ M₀}
    (h : f.comp (Nat.castRingHom ℚ≥0 : ℕ →*₀ ℚ≥0) = g.comp (Nat.castRingHom ℚ≥0)) : f = g :=
  ext_nnrat' <| DFunLike.congr_fun h

lemma ext_nnrat_on_pnat (same_on_pnat : ∀ n : ℕ, 0 < n → f n = g n) : f = g :=
  ext_nnrat' <| DFunLike.congr_fun <| ext_nat''
    ((f : ℚ≥0 →*₀ M₀).comp (Nat.castRingHom ℚ≥0 : ℕ →*₀ ℚ≥0))
    ((g : ℚ≥0 →*₀ M₀).comp (Nat.castRingHom ℚ≥0 : ℕ →*₀ ℚ≥0)) (by simpa)

end NNRat

section Rat

variable [FunLike F ℚ M₀] [MonoidWithZeroHomClass F ℚ M₀] {f g : F}

theorem ext_rat' (h : ∀ m : ℤ, f m = g m) : f = g :=
  (DFunLike.ext f g) fun r => by
    rw [← r.num_div_den, div_eq_mul_inv, map_mul, map_mul, h, ← Int.cast_natCast,
      eq_on_inv₀ f g]
    apply h

@[ext]
theorem ext_rat {f g : ℚ →*₀ M₀}
    (h : f.comp (Int.castRingHom ℚ : ℤ →*₀ ℚ) = g.comp (Int.castRingHom ℚ)) : f = g :=
  ext_rat' <| DFunLike.congr_fun h

theorem ext_rat_on_pnat (same_on_neg_one : f (-1) = g (-1))
    (same_on_pnat : ∀ n : ℕ, 0 < n → f n = g n) : f = g :=
  ext_rat' <|
    DFunLike.congr_fun <|
      show
        (f : ℚ →*₀ M₀).comp (Int.castRingHom ℚ : ℤ →*₀ ℚ) =
          (g : ℚ →*₀ M₀).comp (Int.castRingHom ℚ : ℤ →*₀ ℚ)
        from ext_int' (by simpa) (by simpa)

end Rat

end MonoidWithZeroHomClass

theorem RingHom.ext_rat {R : Type*} [Semiring R] [FunLike F ℚ R] [RingHomClass F ℚ R] (f g : F) :
    f = g :=
  MonoidWithZeroHomClass.ext_rat' <|
    RingHom.congr_fun <|
      ((f : ℚ →+* R).comp (Int.castRingHom ℚ)).ext_int ((g : ℚ →+* R).comp (Int.castRingHom ℚ))

instance NNRat.subsingleton_ringHom {R : Type*} [Semiring R] : Subsingleton (ℚ≥0 →+* R) where
  allEq f g := MonoidWithZeroHomClass.ext_nnrat' <| by simp

instance Rat.subsingleton_ringHom {R : Type*} [Semiring R] : Subsingleton (ℚ →+* R) :=
  ⟨RingHom.ext_rat⟩

/-! ### Scalar multiplication -/

namespace NNRat

variable [DivisionSemiring α]

instance (priority := 100) instDistribSMul : DistribSMul ℚ≥0 α where
  smul_zero a := by rw [smul_def, mul_zero]
  smul_add a x y := by rw [smul_def, smul_def, smul_def, mul_add]

instance instIsScalarTowerRight : IsScalarTower ℚ≥0 α α where
  smul_assoc a x y := by simp only [smul_def, smul_eq_mul, mul_assoc]

end NNRat

namespace Rat

variable [DivisionRing α]

instance (priority := 100) instDistribSMul : DistribSMul ℚ α where
  smul_zero a := by rw [smul_def, mul_zero]
  smul_add a x y := by rw [smul_def, smul_def, smul_def, mul_add]

instance instIsScalarTowerRight : IsScalarTower ℚ α α where
  smul_assoc a x y := by simp only [smul_def, smul_eq_mul, mul_assoc]

end Rat
