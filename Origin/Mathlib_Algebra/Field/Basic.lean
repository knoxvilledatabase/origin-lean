/-
Extracted from Algebra/Field/Basic.lean
Genuine: 20 of 65 | Dissolved: 29 | Infrastructure: 16
-/
import Origin.Core
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Ring.Invertible
import Mathlib.Order.Synonym

/-!
# Lemmas about division (semi)rings and (semi)fields

-/

open Function OrderDual Set

universe u

variable {K L : Type*}

section DivisionSemiring

variable [DivisionSemiring K] {a b c d : K}

theorem add_div (a b c : K) : (a + b) / c = a / c + b / c := by simp_rw [div_eq_mul_inv, add_mul]

@[field_simps]
theorem div_add_div_same (a b c : K) : a / c + b / c = (a + b) / c :=
  (add_div _ _ _).symm

-- DISSOLVED: same_add_div

-- DISSOLVED: div_add_same

-- DISSOLVED: one_add_div

-- DISSOLVED: div_add_one

-- DISSOLVED: inv_add_inv'

-- DISSOLVED: one_div_mul_add_mul_one_div_eq_one_div_add_one_div

-- DISSOLVED: add_div_eq_mul_add_div

-- DISSOLVED: add_div'

-- DISSOLVED: div_add'

-- DISSOLVED: Commute.div_add_div

-- DISSOLVED: Commute.one_div_add_one_div

-- DISSOLVED: Commute.inv_add_inv

end DivisionSemiring

section DivisionMonoid

variable [DivisionMonoid K] [HasDistribNeg K] {a b : K}

theorem one_div_neg_one_eq_neg_one : (1 : K) / -1 = -1 :=
  have : -1 * -1 = (1 : K) := by rw [neg_mul_neg, one_mul]
  Eq.symm (eq_one_div_of_mul_eq_one_right this)

theorem one_div_neg_eq_neg_one_div (a : K) : 1 / -a = -(1 / a) :=
  calc
    1 / -a = 1 / (-1 * a) := by rw [neg_eq_neg_one_mul]
    _ = 1 / a * (1 / -1) := by rw [one_div_mul_one_div_rev]
    _ = 1 / a * -1 := by rw [one_div_neg_one_eq_neg_one]
    _ = -(1 / a) := by rw [mul_neg, mul_one]

theorem div_neg_eq_neg_div (a b : K) : b / -a = -(b / a) :=
  calc
    b / -a = b * (1 / -a) := by rw [← inv_eq_one_div, division_def]
    _ = b * -(1 / a) := by rw [one_div_neg_eq_neg_one_div]
    _ = -(b * (1 / a)) := by rw [neg_mul_eq_mul_neg]
    _ = -(b / a) := by rw [mul_one_div]

theorem neg_div (a b : K) : -b / a = -(b / a) := by
  rw [neg_eq_neg_one_mul, mul_div_assoc, ← neg_eq_neg_one_mul]

@[field_simps]
theorem neg_div' (a b : K) : -(b / a) = -b / a := by simp [neg_div]

@[simp]
theorem neg_div_neg_eq (a b : K) : -a / -b = a / b := by rw [div_neg_eq_neg_div, neg_div, neg_neg]

theorem neg_inv : -a⁻¹ = (-a)⁻¹ := by rw [inv_eq_one_div, inv_eq_one_div, div_neg_eq_neg_div]

theorem div_neg (a : K) : a / -b = -(a / b) := by rw [← div_neg_eq_neg_div]

theorem inv_neg : (-a)⁻¹ = -a⁻¹ := by rw [neg_inv]

theorem inv_neg_one : (-1 : K)⁻¹ = -1 := by rw [← neg_inv, inv_one]

end DivisionMonoid

section DivisionRing

variable [DivisionRing K] {a b c d : K}

-- DISSOLVED: div_neg_self

-- DISSOLVED: neg_div_self

theorem div_sub_div_same (a b c : K) : a / c - b / c = (a - b) / c := by
  rw [sub_eq_add_neg, ← neg_div, div_add_div_same, sub_eq_add_neg]

-- DISSOLVED: same_sub_div

-- DISSOLVED: one_sub_div

-- DISSOLVED: div_sub_same

-- DISSOLVED: div_sub_one

theorem sub_div (a b c : K) : (a - b) / c = a / c - b / c :=
  (div_sub_div_same _ _ _).symm

-- DISSOLVED: inv_sub_inv'

-- DISSOLVED: one_div_mul_sub_mul_one_div_eq_one_div_add_one_div

instance (priority := 100) DivisionRing.isDomain : IsDomain K :=
  NoZeroDivisors.to_isDomain _

-- DISSOLVED: Commute.div_sub_div

-- DISSOLVED: Commute.inv_sub_inv

end DivisionRing

section Semifield

variable [Semifield K] {a b d : K}

-- DISSOLVED: div_add_div

-- DISSOLVED: one_div_add_one_div

-- DISSOLVED: inv_add_inv

end Semifield

section Field

variable [Field K]

attribute [local simp] mul_assoc mul_comm mul_left_comm

-- DISSOLVED: div_sub_div

-- DISSOLVED: inv_sub_inv

-- DISSOLVED: sub_div'

-- DISSOLVED: div_sub'

instance (priority := 100) Field.isDomain : IsDomain K :=
  { DivisionRing.isDomain with }

end Field

section NoncomputableDefs

variable {R : Type*} [Nontrivial R]

noncomputable abbrev DivisionRing.ofIsUnitOrEqZero [Ring R] (h : ∀ a : R, IsUnit a ∨ a = 0) :
    DivisionRing R where
  toRing := ‹Ring R›
  __ := groupWithZeroOfIsUnitOrEqZero h
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

noncomputable abbrev Field.ofIsUnitOrEqZero [CommRing R] (h : ∀ a : R, IsUnit a ∨ a = 0) :
    Field R where
  toCommRing := ‹CommRing R›
  __ := DivisionRing.ofIsUnitOrEqZero h

end NoncomputableDefs

namespace Function.Injective

variable [Zero K] [Add K] [Neg K] [Sub K] [One K] [Mul K] [Inv K] [Div K] [SMul ℕ K] [SMul ℤ K]
  [SMul ℚ≥0 K] [SMul ℚ K] [Pow K ℕ] [Pow K ℤ] [NatCast K] [IntCast K] [NNRatCast K] [RatCast K]
  (f : K → L) (hf : Injective f)

protected abbrev divisionSemiring [DivisionSemiring L] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (inv : ∀ x, f x⁻¹ = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (nnqsmul : ∀ (q : ℚ≥0) (x), f (q • x) = q • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n)
    (natCast : ∀ n : ℕ, f n = n) (nnratCast : ∀ q : ℚ≥0, f q = q) : DivisionSemiring K where
  toSemiring := hf.semiring f zero one add mul nsmul npow natCast
  __ := hf.groupWithZero f zero one mul inv div npow zpow
  nnratCast_def q := hf <| by rw [nnratCast, NNRat.cast_def, div, natCast, natCast]
  nnqsmul := (· • ·)
  nnqsmul_def q a := hf <| by rw [nnqsmul, NNRat.smul_def, mul, nnratCast]

protected abbrev divisionRing [DivisionRing L] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x)
    (nnqsmul : ∀ (q : ℚ≥0) (x), f (q • x) = q • f x) (qsmul : ∀ (q : ℚ) (x), f (q • x) = q • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n)
    (natCast : ∀ n : ℕ, f n = n) (intCast : ∀ n : ℤ, f n = n) (nnratCast : ∀ q : ℚ≥0, f q = q)
    (ratCast : ∀ q : ℚ, f q = q) : DivisionRing K where
  toRing := hf.ring f zero one add mul neg sub nsmul zsmul npow natCast intCast
  __ := hf.groupWithZero f zero one mul inv div npow zpow
  __ := hf.divisionSemiring f zero one add mul inv div nsmul nnqsmul npow zpow natCast nnratCast
  ratCast_def q := hf <| by rw [ratCast, div, intCast, natCast, Rat.cast_def]
  qsmul := (· • ·)
  qsmul_def q a := hf <| by rw [qsmul, mul, Rat.smul_def, ratCast]

protected abbrev semifield [Semifield L] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (inv : ∀ x, f x⁻¹ = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (nnqsmul : ∀ (q : ℚ≥0) (x), f (q • x) = q • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n)
    (natCast : ∀ n : ℕ, f n = n) (nnratCast : ∀ q : ℚ≥0, f q = q) : Semifield K where
  toCommSemiring := hf.commSemiring f zero one add mul nsmul npow natCast
  __ := hf.commGroupWithZero f zero one mul inv div npow zpow
  __ := hf.divisionSemiring f zero one add mul inv div nsmul nnqsmul npow zpow natCast nnratCast

protected abbrev field [Field L] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x)
    (nnqsmul : ∀ (q : ℚ≥0) (x), f (q • x) = q • f x) (qsmul : ∀ (q : ℚ) (x), f (q • x) = q • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n)
    (natCast : ∀ n : ℕ, f n = n) (intCast : ∀ n : ℤ, f n = n) (nnratCast : ∀ q : ℚ≥0, f q = q)
    (ratCast : ∀ q : ℚ, f q = q) :
    Field K where
  toCommRing := hf.commRing f zero one add mul neg sub nsmul zsmul npow natCast intCast
  __ := hf.divisionRing f zero one add mul neg sub inv div nsmul zsmul nnqsmul qsmul npow zpow
    natCast intCast nnratCast ratCast

end Function.Injective

/-! ### Order dual -/

namespace OrderDual

instance instRatCast [RatCast K] : RatCast Kᵒᵈ := ‹_›

instance instDivisionSemiring [DivisionSemiring K] : DivisionSemiring Kᵒᵈ := ‹_›

instance instDivisionRing [DivisionRing K] : DivisionRing Kᵒᵈ := ‹_›

instance instSemifield [Semifield K] : Semifield Kᵒᵈ := ‹_›

instance instField [Field K] : Field Kᵒᵈ := ‹_›

end OrderDual

@[simp] lemma toDual_ratCast [RatCast K] (n : ℚ) : toDual (n : K) = n := rfl

@[simp] lemma ofDual_ratCast [RatCast K] (n : ℚ) : (ofDual n : K) = n := rfl

/-! ### Lexicographic order -/

namespace Lex

instance instRatCast [RatCast K] : RatCast (Lex K) := ‹_›

instance instDivisionSemiring [DivisionSemiring K] : DivisionSemiring (Lex K) := ‹_›

instance instDivisionRing [DivisionRing K] : DivisionRing (Lex K) := ‹_›

instance instSemifield [Semifield K] : Semifield (Lex K) := ‹_›

instance instField [Field K] : Field (Lex K) := ‹_›

end Lex

@[simp] lemma toLex_ratCast [RatCast K] (n : ℚ) : toLex (n : K) = n := rfl

@[simp] lemma ofLex_ratCast [RatCast K] (n : ℚ) : (ofLex n : K) = n := rfl
