/-
Extracted from Data/Rat/Defs.lean
Genuine: 49 | Conflates: 0 | Dissolved: 22 | Infrastructure: 35
-/
import Origin.Core
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Int.Defs
import Mathlib.Data.Rat.Init
import Mathlib.Order.Basic
import Mathlib.Tactic.Common
import Batteries.Data.Rat.Lemmas

/-!
# Basics for the Rational Numbers

## Summary

We define the integral domain structure on `ℚ` and prove basic lemmas about it.
The definition of the field structure on `ℚ` will be done in `Mathlib.Data.Rat.Basic` once the
`Field` class has been defined.

## Main Definitions

- `Rat.divInt n d` constructs a rational number `q = n / d` from `n d : ℤ`.

## Notations

- `/.` is infix notation for `Rat.divInt`.

-/

open Function

namespace Rat

variable {q : ℚ}

theorem pos (a : ℚ) : 0 < a.den := Nat.pos_of_ne_zero a.den_nz

lemma mk'_num_den (q : ℚ) : mk' q.num q.den q.den_nz q.reduced = q := rfl

@[simp]
theorem ofInt_eq_cast (n : ℤ) : ofInt n = Int.cast n :=
  rfl

@[simp] lemma num_ofNat (n : ℕ) : num (no_index (OfNat.ofNat n)) = OfNat.ofNat n := rfl

@[simp] lemma den_ofNat (n : ℕ) : den (no_index (OfNat.ofNat n)) = 1 := rfl

@[simp, norm_cast] lemma num_natCast (n : ℕ) : num n = n := rfl

@[simp, norm_cast] lemma den_natCast (n : ℕ) : den n = 1 := rfl

@[simp, norm_cast] lemma num_intCast (n : ℤ) : (n : ℚ).num = n := rfl

@[simp, norm_cast] lemma den_intCast (n : ℤ) : (n : ℚ).den = 1 := rfl

lemma intCast_injective : Injective (Int.cast : ℤ → ℚ) := fun _ _ ↦ congr_arg num

lemma natCast_injective : Injective (Nat.cast : ℕ → ℚ) :=
  intCast_injective.comp fun _ _ ↦ Int.natCast_inj.1

@[simp, nolint simpNF, norm_cast] lemma natCast_inj {m n : ℕ} : (m : ℚ) = n ↔ m = n :=
  natCast_injective.eq_iff

@[simp, nolint simpNF, norm_cast] lemma intCast_eq_zero {n : ℤ} : (n : ℚ) = 0 ↔ n = 0 := intCast_inj

@[simp, nolint simpNF, norm_cast] lemma natCast_eq_zero {n : ℕ} : (n : ℚ) = 0 ↔ n = 0 := natCast_inj

@[simp, nolint simpNF, norm_cast] lemma intCast_eq_one {n : ℤ} : (n : ℚ) = 1 ↔ n = 1 := intCast_inj

@[simp, nolint simpNF, norm_cast] lemma natCast_eq_one {n : ℕ} : (n : ℚ) = 1 ↔ n = 1 := natCast_inj

lemma mkRat_eq_divInt (n d) : mkRat n d = n /. d := rfl

-- DISSOLVED: mk'_zero

@[simp]
lemma num_eq_zero {q : ℚ} : q.num = 0 ↔ q = 0 := by
  induction q
  constructor
  · rintro rfl
    exact mk'_zero _ _ _
  · exact congr_arg num

-- DISSOLVED: num_ne_zero

-- DISSOLVED: den_ne_zero

@[simp] lemma num_nonneg : 0 ≤ q.num ↔ 0 ≤ q := by
  simp [Int.le_iff_lt_or_eq, instLE, Rat.blt, Int.not_lt]; tauto

-- DISSOLVED: divInt_eq_zero

-- DISSOLVED: divInt_ne_zero

-- DISSOLVED: normalize_eq_mk'

@[simp] alias mkRat_num_den' := mkRat_self
lemma num_divInt_den (q : ℚ) : q.num /. q.den = q := divInt_self _

lemma mk'_eq_divInt {n d h c} : (⟨n, d, h, c⟩ : ℚ) = n /. d := (num_divInt_den _).symm

theorem intCast_eq_divInt (z : ℤ) : (z : ℚ) = z /. 1 := mk'_eq_divInt

-- DISSOLVED: divInt_self'

-- DISSOLVED: numDenCasesOn.{u}

-- DISSOLVED: numDenCasesOn'.{u}

@[elab_as_elim]
def numDenCasesOn''.{u} {C : ℚ → Sort u} (a : ℚ)
    (H : ∀ (n : ℤ) (d : ℕ) (nz red), C (mk' n d nz red)) : C a :=
  numDenCasesOn a fun n d h h' ↦ by rw [← mk_eq_divInt _ _ h.ne' h']; exact H n d h.ne' _

-- DISSOLVED: lift_binop_eq

attribute [simp] divInt_add_divInt

-- DISSOLVED: add_def''

attribute [simp] neg_divInt

lemma neg_def (q : ℚ) : -q = -q.num /. q.den := by rw [← neg_divInt, num_divInt_den]

@[simp] lemma divInt_neg (n d : ℤ) : n /. -d = -n /. d := divInt_neg' ..

attribute [simp] divInt_sub_divInt

-- DISSOLVED: sub_def''

@[simp]
lemma divInt_mul_divInt' (n₁ d₁ n₂ d₂ : ℤ) : (n₁ /. d₁) * (n₂ /. d₂) = (n₁ * n₂) /. (d₁ * d₂) := by
  obtain rfl | h₁ := eq_or_ne d₁ 0
  · simp
  obtain rfl | h₂ := eq_or_ne d₂ 0
  · simp
  exact divInt_mul_divInt _ _ h₁ h₂

attribute [simp] mkRat_mul_mkRat

-- DISSOLVED: mk'_mul_mk'

lemma mul_eq_mkRat (q r : ℚ) : q * r = mkRat (q.num * r.num) (q.den * r.den) := by
  rw [mul_def, normalize_eq_mkRat]

alias divInt_eq_divInt := divInt_eq_iff

instance instPowNat : Pow ℚ ℕ where
  pow q n := ⟨q.num ^ n, q.den ^ n, by simp [Nat.pow_eq_zero], by
    rw [Int.natAbs_pow]; exact q.reduced.pow _ _⟩

lemma pow_def (q : ℚ) (n : ℕ) :
    q ^ n = ⟨q.num ^ n, q.den ^ n,
      by simp [Nat.pow_eq_zero],
      by rw [Int.natAbs_pow]; exact q.reduced.pow _ _⟩ := rfl

lemma pow_eq_mkRat (q : ℚ) (n : ℕ) : q ^ n = mkRat (q.num ^ n) (q.den ^ n) := by
  rw [pow_def, mk_eq_mkRat]

lemma pow_eq_divInt (q : ℚ) (n : ℕ) : q ^ n = q.num ^ n /. q.den ^ n := by
  rw [pow_def, mk_eq_divInt, Int.natCast_pow]

@[simp] lemma num_pow (q : ℚ) (n : ℕ) : (q ^ n).num = q.num ^ n := rfl

@[simp] lemma den_pow (q : ℚ) (n : ℕ) : (q ^ n).den = q.den ^ n := rfl

@[simp] lemma mk'_pow (num : ℤ) (den : ℕ) (hd hdn) (n : ℕ) :
    mk' num den hd hdn ^ n = mk' (num ^ n) (den ^ n)
      (by simp [Nat.pow_eq_zero, hd]) (by rw [Int.natAbs_pow]; exact hdn.pow _ _) := rfl

instance : Inv ℚ :=
  ⟨Rat.inv⟩

@[simp] lemma inv_divInt' (a b : ℤ) : (a /. b)⁻¹ = b /. a := inv_divInt ..

@[simp] lemma inv_mkRat (a : ℤ) (b : ℕ) : (mkRat a b)⁻¹ = b /. a := by
  rw [mkRat_eq_divInt, inv_divInt']

lemma inv_def' (q : ℚ) : q⁻¹ = q.den /. q.num := by rw [← inv_divInt', num_divInt_den]

@[simp] lemma divInt_div_divInt (n₁ d₁ n₂ d₂) :
    (n₁ /. d₁) / (n₂ /. d₂) = (n₁ * d₂) /. (d₁ * n₂) := by
  rw [div_def, inv_divInt, divInt_mul_divInt']

lemma div_def' (q r : ℚ) : q / r = (q.num * r.den) /. (q.den * r.num) := by
  rw [← divInt_div_divInt, num_divInt_den, num_divInt_den]

variable (a b c : ℚ)

protected lemma add_zero : a + 0 = a := by simp [add_def, normalize_eq_mkRat]

protected lemma zero_add : 0 + a = a := by simp [add_def, normalize_eq_mkRat]

protected lemma add_comm : a + b = b + a := by
  simp [add_def, Int.add_comm, Int.mul_comm, Nat.mul_comm]

protected theorem add_assoc : a + b + c = a + (b + c) :=
  numDenCasesOn' a fun n₁ d₁ h₁ ↦ numDenCasesOn' b fun n₂ d₂ h₂ ↦ numDenCasesOn' c fun n₃ d₃ h₃ ↦ by
    simp only [ne_eq, Int.natCast_eq_zero, h₁, not_false_eq_true, h₂, divInt_add_divInt,
      Int.mul_eq_zero, or_self, h₃]
    rw [Int.mul_assoc, Int.add_mul, Int.add_mul, Int.mul_assoc, Int.add_assoc]
    congr 2
    ac_rfl

protected lemma neg_add_cancel : -a + a = 0 := by
  simp [add_def, normalize_eq_mkRat, Int.neg_mul, Int.add_comm, ← Int.sub_eq_add_neg]

lemma divInt_zero_one : 0 /. 1 = 0 := zero_divInt _

@[simp] lemma divInt_one (n : ℤ) : n /. 1 = n := by simp [divInt, mkRat, normalize]

@[simp] lemma mkRat_one (n : ℤ) : mkRat n 1 = n := by simp [mkRat_eq_divInt]

-- DISSOLVED: divInt_one_one

-- DISSOLVED: divInt_neg_one_one

protected theorem mul_assoc : a * b * c = a * (b * c) :=
  numDenCasesOn' a fun n₁ d₁ h₁ =>
    numDenCasesOn' b fun n₂ d₂ h₂ =>
      numDenCasesOn' c fun n₃ d₃ h₃ => by
        simp [h₁, h₂, h₃, Int.mul_comm, Nat.mul_assoc, Int.mul_left_comm]

protected theorem add_mul : (a + b) * c = a * c + b * c :=
  numDenCasesOn' a fun n₁ d₁ h₁ ↦ numDenCasesOn' b fun n₂ d₂ h₂ ↦ numDenCasesOn' c fun n₃ d₃ h₃ ↦ by
    simp only [ne_eq, Int.natCast_eq_zero, h₁, not_false_eq_true, h₂, divInt_add_divInt,
      Int.mul_eq_zero, or_self, h₃, divInt_mul_divInt]
    rw [← divInt_mul_right (Int.natCast_ne_zero.2 h₃), Int.add_mul, Int.add_mul]
    ac_rfl

protected theorem mul_add : a * (b + c) = a * b + a * c := by
  rw [Rat.mul_comm, Rat.add_mul, Rat.mul_comm, Rat.mul_comm c a]

-- DISSOLVED: zero_ne_one

attribute [simp] mkRat_eq_zero

-- DISSOLVED: mul_inv_cancel

-- DISSOLVED: inv_mul_cancel

instance nontrivial : Nontrivial ℚ where exists_pair_ne := ⟨1, 0, by decide⟩

/-! ### The rational numbers are a group -/

instance addCommGroup : AddCommGroup ℚ where
  zero := 0
  add := (· + ·)
  neg := Neg.neg
  zero_add := Rat.zero_add
  add_zero := Rat.add_zero
  add_comm := Rat.add_comm
  add_assoc := Rat.add_assoc
  neg_add_cancel := Rat.neg_add_cancel
  sub_eq_add_neg := Rat.sub_eq_add_neg
  nsmul := nsmulRec
  zsmul := zsmulRec

instance addGroup : AddGroup ℚ := by infer_instance

instance addCommMonoid : AddCommMonoid ℚ := by infer_instance

instance addMonoid : AddMonoid ℚ := by infer_instance

instance addLeftCancelSemigroup : AddLeftCancelSemigroup ℚ := by infer_instance

instance addRightCancelSemigroup : AddRightCancelSemigroup ℚ := by infer_instance

instance addCommSemigroup : AddCommSemigroup ℚ := by infer_instance

instance addSemigroup : AddSemigroup ℚ := by infer_instance

instance commMonoid : CommMonoid ℚ where
  one := 1
  mul := (· * ·)
  mul_one := Rat.mul_one
  one_mul := Rat.one_mul
  mul_comm := Rat.mul_comm
  mul_assoc := Rat.mul_assoc
  npow n q := q ^ n
  npow_zero := by intros; apply Rat.ext <;> simp [Int.pow_zero]
  npow_succ n q := by
    dsimp
    rw [← q.mk'_num_den, mk'_pow, mk'_mul_mk']
    · congr
    · rw [mk'_pow, Int.natAbs_pow]
      exact q.reduced.pow_left _
    · rw [mk'_pow]
      exact q.reduced.pow_right _

instance monoid : Monoid ℚ := by infer_instance

instance commSemigroup : CommSemigroup ℚ := by infer_instance

instance semigroup : Semigroup ℚ := by infer_instance

theorem eq_iff_mul_eq_mul {p q : ℚ} : p = q ↔ p.num * q.den = q.num * p.den := by
  conv =>
    lhs
    rw [← num_divInt_den p, ← num_divInt_den q]
  apply Rat.divInt_eq_iff <;>
    · rw [← Int.natCast_zero, Ne, Int.ofNat_inj]
      apply den_nz

@[simp]
theorem den_neg_eq_den (q : ℚ) : (-q).den = q.den :=
  rfl

@[simp]
theorem num_neg_eq_neg_num (q : ℚ) : (-q).num = -q.num :=
  rfl

@[simp]
theorem num_zero : Rat.num 0 = 0 :=
  rfl

@[simp]
theorem den_zero : Rat.den 0 = 1 :=
  rfl

lemma zero_of_num_zero {q : ℚ} (hq : q.num = 0) : q = 0 := by simpa [hq] using q.num_divInt_den.symm

theorem zero_iff_num_zero {q : ℚ} : q = 0 ↔ q.num = 0 :=
  ⟨fun _ => by simp [*], zero_of_num_zero⟩

@[simp]
theorem num_one : (1 : ℚ).num = 1 :=
  rfl

@[simp]
theorem den_one : (1 : ℚ).den = 1 :=
  rfl

-- DISSOLVED: mk_num_ne_zero_of_ne_zero

-- DISSOLVED: mk_denom_ne_zero_of_ne_zero

-- DISSOLVED: divInt_ne_zero_of_ne_zero

protected lemma nonneg_antisymm : 0 ≤ q → 0 ≤ -q → q = 0 := by
  simp_rw [← num_eq_zero, Int.le_antisymm_iff, ← num_nonneg, num_neg_eq_neg_num, Int.neg_nonneg]
  tauto

protected lemma nonneg_total (a : ℚ) : 0 ≤ a ∨ 0 ≤ -a := by
  simp_rw [← num_nonneg, num_neg_eq_neg_num, Int.neg_nonneg]; exact Int.le_total _ _

section Casts

protected theorem add_divInt (a b c : ℤ) : (a + b) /. c = a /. c + b /. c :=
  if h : c = 0 then by simp [h]
  else by
    rw [divInt_add_divInt _ _ h h, divInt_eq_iff h (Int.mul_ne_zero h h)]
    simp [Int.add_mul, Int.mul_assoc]

theorem divInt_eq_div (n d : ℤ) : n /. d = (n : ℚ) / d := by simp [div_def']

lemma intCast_div_eq_divInt (n d : ℤ) : (n : ℚ) / (d) = n /. d := by rw [divInt_eq_div]

theorem natCast_div_eq_divInt (n d : ℕ) : (n : ℚ) / d = n /. d := Rat.intCast_div_eq_divInt n d

-- DISSOLVED: divInt_mul_divInt_cancel

theorem coe_int_num_of_den_eq_one {q : ℚ} (hq : q.den = 1) : (q.num : ℚ) = q := by
  conv_rhs => rw [← num_divInt_den q, hq]
  rw [intCast_eq_divInt]
  rfl

lemma eq_num_of_isInt {q : ℚ} (h : q.isInt) : q = q.num := by
  rw [Rat.isInt, Nat.beq_eq_true_eq] at h
  exact (Rat.coe_int_num_of_den_eq_one h).symm

theorem den_eq_one_iff (r : ℚ) : r.den = 1 ↔ ↑r.num = r :=
  ⟨Rat.coe_int_num_of_den_eq_one, fun h => h ▸ Rat.den_intCast r.num⟩

instance canLift : CanLift ℚ ℤ (↑) fun q => q.den = 1 :=
  ⟨fun q hq => ⟨q.num, coe_int_num_of_den_eq_one hq⟩⟩

theorem coe_int_inj (m n : ℤ) : (m : ℚ) = n ↔ m = n :=
  ⟨congr_arg num, congr_arg _⟩

end Casts

end Rat
