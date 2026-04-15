/-
Extracted from Data/ENNReal/Inv.lean
Genuine: 116 of 184 | Dissolved: 58 | Infrastructure: 10
-/
import Origin.Core
import Mathlib.Data.ENNReal.Operations

/-!
# Results about division in extended non-negative reals

This file establishes basic properties related to the inversion and division operations on `ℝ≥0∞`.
For instance, as a consequence of being a `DivInvOneMonoid`, `ℝ≥0∞` inherits a power operation
with integer exponent.

## Main results

A few order isomorphisms are worthy of mention:

  - `OrderIso.invENNReal : ℝ≥0∞ ≃o ℝ≥0∞ᵒᵈ`: The map `x ↦ x⁻¹` as an order isomorphism to the dual.

  - `orderIsoIicOneBirational : ℝ≥0∞ ≃o Iic (1 : ℝ≥0∞)`: The birational order isomorphism between
    `ℝ≥0∞` and the unit interval `Set.Iic (1 : ℝ≥0∞)` given by `x ↦ (x⁻¹ + 1)⁻¹` with inverse
    `x ↦ (x⁻¹ - 1)⁻¹`

  - `orderIsoIicCoe (a : ℝ≥0) : Iic (a : ℝ≥0∞) ≃o Iic a`: Order isomorphism between an initial
    interval in `ℝ≥0∞` and an initial interval in `ℝ≥0` given by the identity map.

  - `orderIsoUnitIntervalBirational : ℝ≥0∞ ≃o Icc (0 : ℝ) 1`: An order isomorphism between
    the extended nonnegative real numbers and the unit interval. This is `orderIsoIicOneBirational`
    composed with the identity order isomorphism between `Iic (1 : ℝ≥0∞)` and `Icc (0 : ℝ) 1`.
-/

open Set NNReal

namespace ENNReal

noncomputable section Inv

variable {a b c d : ℝ≥0∞} {r p q : ℝ≥0}

protected theorem div_eq_inv_mul : a / b = b⁻¹ * a := by rw [div_eq_mul_inv, mul_comm]

-- DISSOLVED: inv_zero

@[simp] theorem inv_top : ∞⁻¹ = 0 :=
  bot_unique <| le_of_forall_le_of_dense fun a (h : 0 < a) => sInf_le <| by simp [*, h.ne', top_mul]

theorem coe_inv_le : (↑r⁻¹ : ℝ≥0∞) ≤ (↑r)⁻¹ :=
  le_sInf fun b (hb : 1 ≤ ↑r * b) =>
    coe_le_iff.2 <| by
      rintro b rfl
      apply NNReal.inv_le_of_le_mul
      rwa [← coe_mul, ← coe_one, coe_le_coe] at hb

-- DISSOLVED: coe_inv

@[norm_cast]
theorem coe_inv_two : ((2⁻¹ : ℝ≥0) : ℝ≥0∞) = 2⁻¹ := by rw [coe_inv _root_.two_ne_zero, coe_two]

-- DISSOLVED: coe_div

lemma coe_div_le : ↑(p / r) ≤ (p / r : ℝ≥0∞) := by
  simpa only [div_eq_mul_inv, coe_mul] using mul_le_mul_left' coe_inv_le _

-- DISSOLVED: div_zero

instance : DivInvOneMonoid ℝ≥0∞ :=
  { inferInstanceAs (DivInvMonoid ℝ≥0∞) with
    inv_one := by simpa only [coe_inv one_ne_zero, coe_one] using coe_inj.2 inv_one }

protected theorem inv_pow : ∀ {a : ℝ≥0∞} {n : ℕ}, (a ^ n)⁻¹ = a⁻¹ ^ n
  | _, 0 => by simp only [pow_zero, inv_one]
  | ⊤, n + 1 => by simp [top_pow]
  | (a : ℝ≥0), n + 1 => by
    rcases eq_or_ne a 0 with (rfl | ha)
    · simp [top_pow]
    · have := pow_ne_zero (n + 1) ha
      norm_cast
      rw [inv_pow]

-- DISSOLVED: mul_inv_cancel

-- DISSOLVED: inv_mul_cancel

-- DISSOLVED: div_mul_cancel

-- DISSOLVED: mul_div_cancel'

protected theorem mul_comm_div : a / b * c = a * (c / b) := by
  simp only [div_eq_mul_inv, mul_right_comm, ← mul_assoc]

protected theorem mul_div_right_comm : a * b / c = a / c * b := by
  simp only [div_eq_mul_inv, mul_right_comm]

instance : InvolutiveInv ℝ≥0∞ where
  inv_inv a := by
    by_cases a = 0 <;> cases a <;> simp_all [none_eq_top, some_eq_coe, -coe_inv, (coe_inv _).symm]

@[simp] protected lemma inv_eq_one : a⁻¹ = 1 ↔ a = 1 := by rw [← inv_inj, inv_inv, inv_one]

@[simp] theorem inv_eq_top : a⁻¹ = ∞ ↔ a = 0 := inv_zero ▸ inv_inj

-- DISSOLVED: inv_ne_top

protected alias ⟨_, Finiteness.inv_ne_top⟩ := ENNReal.inv_ne_top

@[simp]
theorem inv_lt_top {x : ℝ≥0∞} : x⁻¹ < ∞ ↔ 0 < x := by
  simp only [lt_top_iff_ne_top, inv_ne_top, pos_iff_ne_zero]

-- DISSOLVED: div_lt_top

@[simp]
protected theorem inv_eq_zero : a⁻¹ = 0 ↔ a = ∞ :=
  inv_top ▸ inv_inj

-- DISSOLVED: inv_ne_zero

-- DISSOLVED: div_pos

-- DISSOLVED: inv_mul_le_iff

-- DISSOLVED: mul_inv_le_iff

-- DISSOLVED: div_le_iff

-- DISSOLVED: div_le_iff'

-- DISSOLVED: mul_inv

-- DISSOLVED: inv_div

-- DISSOLVED: prod_inv_distrib

-- DISSOLVED: mul_div_mul_left

-- DISSOLVED: mul_div_mul_right

-- DISSOLVED: sub_div

@[simp]
protected theorem inv_pos : 0 < a⁻¹ ↔ a ≠ ∞ :=
  pos_iff_ne_zero.trans ENNReal.inv_ne_zero

theorem inv_strictAnti : StrictAnti (Inv.inv : ℝ≥0∞ → ℝ≥0∞) := by
  intro a b h
  lift a to ℝ≥0 using h.ne_top
  induction b; · simp
  rw [coe_lt_coe] at h
  rcases eq_or_ne a 0 with (rfl | ha); · simp [h]
  rw [← coe_inv h.ne_bot, ← coe_inv ha, coe_lt_coe]
  exact NNReal.inv_lt_inv ha h

@[simp]
protected theorem inv_lt_inv : a⁻¹ < b⁻¹ ↔ b < a :=
  inv_strictAnti.lt_iff_lt

theorem inv_lt_iff_inv_lt : a⁻¹ < b ↔ b⁻¹ < a := by
  simpa only [inv_inv] using @ENNReal.inv_lt_inv a b⁻¹

theorem lt_inv_iff_lt_inv : a < b⁻¹ ↔ b < a⁻¹ := by
  simpa only [inv_inv] using @ENNReal.inv_lt_inv a⁻¹ b

@[simp]
protected theorem inv_le_inv : a⁻¹ ≤ b⁻¹ ↔ b ≤ a :=
  inv_strictAnti.le_iff_le

theorem inv_le_iff_inv_le : a⁻¹ ≤ b ↔ b⁻¹ ≤ a := by
  simpa only [inv_inv] using @ENNReal.inv_le_inv a b⁻¹

theorem le_inv_iff_le_inv : a ≤ b⁻¹ ↔ b ≤ a⁻¹ := by
  simpa only [inv_inv] using @ENNReal.inv_le_inv a⁻¹ b

@[gcongr] protected theorem inv_le_inv' (h : a ≤ b) : b⁻¹ ≤ a⁻¹ :=
  ENNReal.inv_strictAnti.antitone h

@[gcongr] protected theorem inv_lt_inv' (h : a < b) : b⁻¹ < a⁻¹ := ENNReal.inv_strictAnti h

@[simp]
protected theorem inv_le_one : a⁻¹ ≤ 1 ↔ 1 ≤ a := by rw [inv_le_iff_inv_le, inv_one]

protected theorem one_le_inv : 1 ≤ a⁻¹ ↔ a ≤ 1 := by rw [le_inv_iff_le_inv, inv_one]

@[simp]
protected theorem inv_lt_one : a⁻¹ < 1 ↔ 1 < a := by rw [inv_lt_iff_inv_lt, inv_one]

@[simp]
protected theorem one_lt_inv : 1 < a⁻¹ ↔ a < 1 := by rw [lt_inv_iff_lt_inv, inv_one]

@[simps! apply]
def _root_.OrderIso.invENNReal : ℝ≥0∞ ≃o ℝ≥0∞ᵒᵈ where
  map_rel_iff' := ENNReal.inv_le_inv
  toEquiv := (Equiv.inv ℝ≥0∞).trans OrderDual.toDual

@[simp]
theorem _root_.OrderIso.invENNReal_symm_apply (a : ℝ≥0∞ᵒᵈ) :
    OrderIso.invENNReal.symm a = (OrderDual.ofDual a)⁻¹ :=
  rfl

@[simp] theorem div_top : a / ∞ = 0 := by rw [div_eq_mul_inv, inv_top, mul_zero]

theorem top_div : ∞ / a = if a = ∞ then 0 else ∞ := by simp [div_eq_mul_inv, top_mul']

theorem top_div_of_ne_top (h : a ≠ ∞) : ∞ / a = ∞ := by simp [top_div, h]

@[simp] theorem top_div_coe : ∞ / p = ∞ := top_div_of_ne_top coe_ne_top

theorem top_div_of_lt_top (h : a < ∞) : ∞ / a = ∞ := top_div_of_ne_top h.ne

-- DISSOLVED: zero_div

-- DISSOLVED: div_eq_top

-- DISSOLVED: le_div_iff_mul_le

-- DISSOLVED: div_le_iff_le_mul

-- DISSOLVED: lt_div_iff_mul_lt

theorem div_le_of_le_mul (h : a ≤ b * c) : a / c ≤ b := by
  by_cases h0 : c = 0
  · have : a = 0 := by simpa [h0] using h
    simp [*]
  by_cases hinf : c = ∞; · simp [hinf]
  exact (ENNReal.div_le_iff_le_mul (Or.inl h0) (Or.inl hinf)).2 h

theorem div_le_of_le_mul' (h : a ≤ b * c) : a / b ≤ c :=
  div_le_of_le_mul <| mul_comm b c ▸ h

@[simp] protected theorem div_self_le_one : a / a ≤ 1 := div_le_of_le_mul <| by rw [one_mul]

@[simp] protected lemma mul_inv_le_one (a : ℝ≥0∞) : a * a⁻¹ ≤ 1 := ENNReal.div_self_le_one

@[simp] protected lemma inv_mul_le_one (a : ℝ≥0∞) : a⁻¹ * a ≤ 1 := by simp [mul_comm]

@[simp] lemma mul_inv_ne_top (a : ℝ≥0∞) : a * a⁻¹ ≠ ⊤ :=
  ne_top_of_le_ne_top one_ne_top a.mul_inv_le_one

@[simp] lemma inv_mul_ne_top (a : ℝ≥0∞) : a⁻¹ * a ≠ ⊤ := by simp [mul_comm]

theorem mul_le_of_le_div (h : a ≤ b / c) : a * c ≤ b := by
  rw [← inv_inv c]
  exact div_le_of_le_mul h

theorem mul_le_of_le_div' (h : a ≤ b / c) : c * a ≤ b :=
  mul_comm a c ▸ mul_le_of_le_div h

-- DISSOLVED: div_lt_iff

theorem mul_lt_of_lt_div (h : a < b / c) : a * c < b := by
  contrapose! h
  exact ENNReal.div_le_of_le_mul h

theorem mul_lt_of_lt_div' (h : a < b / c) : c * a < b :=
  mul_comm a c ▸ mul_lt_of_lt_div h

theorem div_lt_of_lt_mul (h : a < b * c) : a / c < b :=
  mul_lt_of_lt_div <| by rwa [div_eq_mul_inv, inv_inv]

theorem div_lt_of_lt_mul' (h : a < b * c) : a / b < c :=
  div_lt_of_lt_mul <| by rwa [mul_comm]

-- DISSOLVED: inv_le_iff_le_mul

@[simp 900]
theorem le_inv_iff_mul_le : a ≤ b⁻¹ ↔ a * b ≤ 1 := by
  rw [← one_div, ENNReal.le_div_iff_mul_le] <;>
    · right
      simp

@[gcongr] protected theorem div_le_div (hab : a ≤ b) (hdc : d ≤ c) : a / c ≤ b / d :=
  div_eq_mul_inv b d ▸ div_eq_mul_inv a c ▸ mul_le_mul' hab (ENNReal.inv_le_inv.mpr hdc)

@[gcongr] protected theorem div_le_div_left (h : a ≤ b) (c : ℝ≥0∞) : c / b ≤ c / a :=
  ENNReal.div_le_div le_rfl h

@[gcongr] protected theorem div_le_div_right (h : a ≤ b) (c : ℝ≥0∞) : a / c ≤ b / c :=
  ENNReal.div_le_div h le_rfl

protected theorem eq_inv_of_mul_eq_one_left (h : a * b = 1) : a = b⁻¹ := by
  rw [← mul_one a, ← ENNReal.mul_inv_cancel (right_ne_zero_of_mul_eq_one h), ← mul_assoc, h,
    one_mul]
  rintro rfl
  simp [left_ne_zero_of_mul_eq_one h] at h

-- DISSOLVED: mul_le_iff_le_inv

instance : PosSMulStrictMono ℝ≥0 ℝ≥0∞ where
  elim _r hr _a _b hab := ENNReal.mul_lt_mul_left' (coe_pos.2 hr).ne' coe_ne_top hab

instance : SMulPosMono ℝ≥0 ℝ≥0∞ where
  elim _r _ _a _b hab := mul_le_mul_right' (coe_le_coe.2 hab) _

theorem le_of_forall_nnreal_lt {x y : ℝ≥0∞} (h : ∀ r : ℝ≥0, ↑r < x → ↑r ≤ y) : x ≤ y := by
  refine le_of_forall_ge_of_dense fun r hr => ?_
  lift r to ℝ≥0 using ne_top_of_lt hr
  exact h r hr

theorem le_of_forall_pos_nnreal_lt {x y : ℝ≥0∞} (h : ∀ r : ℝ≥0, 0 < r → ↑r < x → ↑r ≤ y) : x ≤ y :=
  le_of_forall_nnreal_lt fun r hr =>
    (zero_le r).eq_or_lt.elim (fun h => h ▸ zero_le _) fun h0 => h r h0 hr

theorem eq_top_of_forall_nnreal_le {x : ℝ≥0∞} (h : ∀ r : ℝ≥0, ↑r ≤ x) : x = ∞ :=
  top_unique <| le_of_forall_nnreal_lt fun r _ => h r

protected theorem add_div : (a + b) / c = a / c + b / c :=
  right_distrib a b c⁻¹

protected theorem div_add_div_same {a b c : ℝ≥0∞} : a / c + b / c = (a + b) / c :=
  ENNReal.add_div.symm

-- DISSOLVED: div_self

theorem mul_div_le : a * (b / a) ≤ b :=
  mul_le_of_le_div' le_rfl

-- DISSOLVED: eq_div_iff

-- DISSOLVED: div_eq_div_iff

-- DISSOLVED: div_eq_one_iff

theorem inv_two_add_inv_two : (2 : ℝ≥0∞)⁻¹ + 2⁻¹ = 1 := by
  rw [← two_mul, ← div_eq_mul_inv, ENNReal.div_self two_ne_zero two_ne_top]

theorem inv_three_add_inv_three : (3 : ℝ≥0∞)⁻¹ + 3⁻¹ + 3⁻¹ = 1 :=
  calc (3 : ℝ≥0∞)⁻¹ + 3⁻¹ + 3⁻¹ = 3 * 3⁻¹ := by ring
  _ = 1 := ENNReal.mul_inv_cancel (Nat.cast_ne_zero.2 <| by decide) coe_ne_top

@[simp]
protected theorem add_halves (a : ℝ≥0∞) : a / 2 + a / 2 = a := by
  rw [div_eq_mul_inv, ← mul_add, inv_two_add_inv_two, mul_one]

@[simp]
theorem add_thirds (a : ℝ≥0∞) : a / 3 + a / 3 + a / 3 = a := by
  rw [div_eq_mul_inv, ← mul_add, ← mul_add, inv_three_add_inv_three, mul_one]

@[simp] theorem div_eq_zero_iff : a / b = 0 ↔ a = 0 ∨ b = ∞ := by simp [div_eq_mul_inv]

-- DISSOLVED: div_pos_iff

-- DISSOLVED: div_ne_zero

-- DISSOLVED: half_pos

protected theorem one_half_lt_one : (2⁻¹ : ℝ≥0∞) < 1 :=
  ENNReal.inv_lt_one.2 <| one_lt_two

-- DISSOLVED: half_lt_self

protected theorem half_le_self : a / 2 ≤ a :=
  le_add_self.trans_eq <| ENNReal.add_halves _

theorem sub_half (h : a ≠ ∞) : a - a / 2 = a / 2 := ENNReal.sub_eq_of_eq_add' h a.add_halves.symm

@[simp]
theorem one_sub_inv_two : (1 : ℝ≥0∞) - 2⁻¹ = 2⁻¹ := by
  simpa only [div_eq_mul_inv, one_mul] using sub_half one_ne_top

private lemma exists_lt_mul_left {a b c : ℝ≥0∞} (hc : c < a * b) : ∃ a' < a, c < a' * b := by
  obtain ⟨a', hc, ha'⟩ := exists_between (ENNReal.div_lt_of_lt_mul hc)
  exact ⟨_, ha', (ENNReal.div_lt_iff (.inl <| by rintro rfl; simp at *)
    (.inr <| by rintro rfl; simp at *)).1 hc⟩

private lemma exists_lt_mul_right {a b c : ℝ≥0∞} (hc : c < a * b) : ∃ b' < b, c < a * b' := by
  simp_rw [mul_comm a] at hc ⊢; exact exists_lt_mul_left hc

lemma mul_le_of_forall_lt {a b c : ℝ≥0∞} (h : ∀ a' < a, ∀ b' < b, a' * b' ≤ c) : a * b ≤ c := by
  refine le_of_forall_ge_of_dense fun d hd ↦ ?_
  obtain ⟨a', ha', hd⟩ := exists_lt_mul_left hd
  obtain ⟨b', hb', hd⟩ := exists_lt_mul_right hd
  exact le_trans hd.le <| h _ ha' _ hb'

-- DISSOLVED: le_mul_of_forall_lt

@[simps! apply_coe]
def orderIsoIicOneBirational : ℝ≥0∞ ≃o Iic (1 : ℝ≥0∞) := by
  refine StrictMono.orderIsoOfRightInverse
    (fun x => ⟨(x⁻¹ + 1)⁻¹, ENNReal.inv_le_one.2 <| le_add_self⟩)
    (fun x y hxy => ?_) (fun x => (x.1⁻¹ - 1)⁻¹) fun x => Subtype.ext ?_
  · simpa only [Subtype.mk_lt_mk, ENNReal.inv_lt_inv, ENNReal.add_lt_add_iff_right one_ne_top]
  · have : (1 : ℝ≥0∞) ≤ x.1⁻¹ := ENNReal.one_le_inv.2 x.2
    simp only [inv_inv, Subtype.coe_mk, tsub_add_cancel_of_le this]

@[simp]
theorem orderIsoIicOneBirational_symm_apply (x : Iic (1 : ℝ≥0∞)) :
    orderIsoIicOneBirational.symm x = (x.1⁻¹ - 1)⁻¹ :=
  rfl

@[simps! apply_coe]
def orderIsoIicCoe (a : ℝ≥0) : Iic (a : ℝ≥0∞) ≃o Iic a :=
  OrderIso.symm
    { toFun := fun x => ⟨x, coe_le_coe.2 x.2⟩
      invFun := fun x => ⟨ENNReal.toNNReal x, coe_le_coe.1 <| coe_toNNReal_le_self.trans x.2⟩
      left_inv := fun _ => Subtype.ext <| toNNReal_coe _
      right_inv := fun x => Subtype.ext <| coe_toNNReal (ne_top_of_le_ne_top coe_ne_top x.2)
      map_rel_iff' := fun {_ _} => by
        simp only [Equiv.coe_fn_mk, Subtype.mk_le_mk, coe_le_coe, Subtype.coe_le_coe] }

@[simp]
theorem orderIsoIicCoe_symm_apply_coe (a : ℝ≥0) (b : Iic a) :
    ((orderIsoIicCoe a).symm b : ℝ≥0∞) = b :=
  rfl

def orderIsoUnitIntervalBirational : ℝ≥0∞ ≃o Icc (0 : ℝ) 1 :=
  orderIsoIicOneBirational.trans <| (orderIsoIicCoe 1).trans <| (NNReal.orderIsoIccZeroCoe 1).symm

@[simp]
theorem orderIsoUnitIntervalBirational_apply_coe (x : ℝ≥0∞) :
    (orderIsoUnitIntervalBirational x : ℝ) = (x⁻¹ + 1)⁻¹.toReal :=
  rfl

-- DISSOLVED: exists_inv_nat_lt

-- DISSOLVED: exists_nat_pos_mul_gt

-- DISSOLVED: exists_nat_mul_gt

-- DISSOLVED: exists_nat_pos_inv_mul_lt

-- DISSOLVED: exists_nnreal_pos_mul_lt

-- DISSOLVED: exists_inv_two_pow_lt

-- DISSOLVED: coe_zpow

-- DISSOLVED: zpow_pos

-- DISSOLVED: zpow_lt_top

-- DISSOLVED: exists_mem_Ico_zpow

-- DISSOLVED: exists_mem_Ioc_zpow

theorem Ioo_zero_top_eq_iUnion_Ico_zpow {y : ℝ≥0∞} (hy : 1 < y) (h'y : y ≠ ⊤) :
    Ioo (0 : ℝ≥0∞) (∞ : ℝ≥0∞) = ⋃ n : ℤ, Ico (y ^ n) (y ^ (n + 1)) := by
  ext x
  simp only [mem_iUnion, mem_Ioo, mem_Ico]
  constructor
  · rintro ⟨hx, h'x⟩
    exact exists_mem_Ico_zpow hx.ne' h'x.ne hy h'y
  · rintro ⟨n, hn, h'n⟩
    constructor
    · apply lt_of_lt_of_le _ hn
      exact ENNReal.zpow_pos (zero_lt_one.trans hy).ne' h'y _
    · apply lt_trans h'n _
      exact ENNReal.zpow_lt_top (zero_lt_one.trans hy).ne' h'y _

@[gcongr]
theorem zpow_le_of_le {x : ℝ≥0∞} (hx : 1 ≤ x) {a b : ℤ} (h : a ≤ b) : x ^ a ≤ x ^ b := by
  induction' a with a a <;> induction' b with b b
  · simp only [Int.ofNat_eq_coe, zpow_natCast]
    exact pow_right_mono₀ hx (Int.le_of_ofNat_le_ofNat h)
  · apply absurd h (not_le_of_gt _)
    exact lt_of_lt_of_le (Int.negSucc_lt_zero _) (Int.ofNat_nonneg _)
  · simp only [zpow_negSucc, Int.ofNat_eq_coe, zpow_natCast]
    refine (ENNReal.inv_le_one.2 ?_).trans ?_ <;> exact one_le_pow_of_one_le' hx _
  · simp only [zpow_negSucc, ENNReal.inv_le_inv]
    apply pow_right_mono₀ hx
    simpa only [← Int.ofNat_le, neg_le_neg_iff, Int.ofNat_add, Int.ofNat_one, Int.negSucc_eq] using
      h

theorem monotone_zpow {x : ℝ≥0∞} (hx : 1 ≤ x) : Monotone ((x ^ ·) : ℤ → ℝ≥0∞) := fun _ _ h =>
  zpow_le_of_le hx h

-- DISSOLVED: zpow_add

-- DISSOLVED: zpow_neg

-- DISSOLVED: zpow_sub

variable {ι κ : Sort*} {f g : ι → ℝ≥0∞} {s : Set ℝ≥0∞} {a : ℝ≥0∞}

@[simp] lemma iSup_eq_zero : ⨆ i, f i = 0 ↔ ∀ i, f i = 0 := iSup_eq_bot

@[simp] lemma iSup_zero : ⨆ _ : ι, (0 : ℝ≥0∞) = 0 := by simp

alias iSup_zero_eq_zero := iSup_zero

lemma iSup_natCast : ⨆ n : ℕ, (n : ℝ≥0∞) = ∞ :=
  (iSup_eq_top _).2 fun _b hb => ENNReal.exists_nat_gt (lt_top_iff_ne_top.1 hb)

@[simp] lemma iSup_lt_eq_self (a : ℝ≥0∞) : ⨆ b, ⨆ _ : b < a, b = a := by
  refine le_antisymm (iSup₂_le fun b hb ↦ hb.le) ?_
  refine le_of_forall_lt fun c hca ↦ ?_
  obtain ⟨d, hcd, hdb⟩ := exists_between hca
  exact hcd.trans_le <| le_iSup₂_of_le d hdb le_rfl

-- DISSOLVED: isUnit_iff

@[simps! toEquiv apply symm_apply]
def mulLeftOrderIso (a  : ℝ≥0∞) (ha : IsUnit a) : ℝ≥0∞ ≃o ℝ≥0∞ where
  toEquiv := ha.unit.mulLeft
  map_rel_iff' := by simp [ENNReal.mul_le_mul_left, ha.ne_zero, (isUnit_iff.1 ha).2]

@[simps! toEquiv apply symm_apply]
def mulRightOrderIso (a  : ℝ≥0∞) (ha : IsUnit a) : ℝ≥0∞ ≃o ℝ≥0∞ where
  toEquiv := ha.unit.mulRight
  map_rel_iff' := by simp [ENNReal.mul_le_mul_right, ha.ne_zero, (isUnit_iff.1 ha).2]

lemma mul_iSup (a : ℝ≥0∞) (f : ι → ℝ≥0∞) : a * ⨆ i, f i = ⨆ i, a * f i := by
  by_cases hf : ∀ i, f i = 0
  · simp [hf]
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp
  obtain rfl | ha := eq_or_ne a ∞
  · obtain ⟨i, hi⟩ := not_forall.1 hf
    simpa [iSup_eq_zero.not.2 hf, eq_comm (a := ⊤)]
      using le_iSup_of_le (f := fun i => ⊤ * f i) i (top_mul hi).ge
  · exact (mulLeftOrderIso _ <| isUnit_iff.2 ⟨ha₀, ha⟩).map_iSup _

lemma iSup_mul (f : ι → ℝ≥0∞) (a : ℝ≥0∞) : (⨆ i, f i) * a = ⨆ i, f i * a := by
  simp [mul_comm, mul_iSup]

lemma mul_sSup {a : ℝ≥0∞} : a * sSup s = ⨆ b ∈ s, a * b := by
  simp only [sSup_eq_iSup, mul_iSup]

lemma sSup_mul {a : ℝ≥0∞} : sSup s * a = ⨆ b ∈ s, b * a := by
  simp only [sSup_eq_iSup, iSup_mul]

lemma iSup_div (f : ι → ℝ≥0∞) (a : ℝ≥0∞) : iSup f / a = ⨆ i, f i / a := iSup_mul ..

lemma sSup_div (s : Set ℝ≥0∞) (a : ℝ≥0∞) : sSup s / a = ⨆ b ∈ s, b / a := sSup_mul ..

lemma mul_iInf' (hinfty : a = ∞ → ⨅ i, f i = 0 → ∃ i, f i = 0) (h₀ : a = 0 → Nonempty ι) :
    a * ⨅ i, f i = ⨅ i, a * f i := by
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp [h₀ rfl]
  obtain rfl | ha := eq_or_ne a ∞
  · obtain ⟨i, hi⟩ | hf := em (∃ i, f i = 0)
    · rw [(iInf_eq_bot _).2, (iInf_eq_bot _).2, bot_eq_zero, mul_zero] <;>
        exact fun _ _↦ ⟨i, by simpa [hi]⟩
    · rw [top_mul (mt (hinfty rfl) hf), eq_comm, iInf_eq_top]
      exact fun i ↦ top_mul fun hi ↦ hf ⟨i, hi⟩
  · exact (mulLeftOrderIso _ <| isUnit_iff.2 ⟨ha₀, ha⟩).map_iInf _

lemma iInf_mul' (hinfty : a = ∞ → ⨅ i, f i = 0 → ∃ i, f i = 0) (h₀ : a = 0 → Nonempty ι) :
    (⨅ i, f i) * a = ⨅ i, f i * a := by simpa only [mul_comm a] using mul_iInf' hinfty h₀

-- DISSOLVED: mul_iInf_of_ne

-- DISSOLVED: iInf_mul_of_ne

lemma mul_iInf [Nonempty ι] (hinfty : a = ∞ → ⨅ i, f i = 0 → ∃ i, f i = 0) :
    a * ⨅ i, f i = ⨅ i, a * f i := mul_iInf' hinfty fun _ ↦ ‹Nonempty ι›

lemma iInf_mul [Nonempty ι] (hinfty : a = ∞ → ⨅ i, f i = 0 → ∃ i, f i = 0) :
    (⨅ i, f i) * a = ⨅ i, f i * a := iInf_mul' hinfty fun _ ↦ ‹Nonempty ι›

lemma iInf_div' (hinfty : a = 0 → ⨅ i, f i = 0 → ∃ i, f i = 0) (h₀ : a = ∞ → Nonempty ι) :
    (⨅ i, f i) / a = ⨅ i, f i / a := iInf_mul' (by simpa) (by simpa)

-- DISSOLVED: iInf_div_of_ne

lemma iInf_div [Nonempty ι] (hinfty : a = 0 → ⨅ i, f i = 0 → ∃ i, f i = 0) :
    (⨅ i, f i) / a = ⨅ i, f i / a := iInf_div' hinfty fun _ ↦ ‹Nonempty ι›

lemma inv_iInf (f : ι → ℝ≥0∞) : (⨅ i, f i)⁻¹ = ⨆ i, (f i)⁻¹ := OrderIso.invENNReal.map_iInf _

lemma inv_iSup (f : ι → ℝ≥0∞) : (⨆ i, f i)⁻¹ = ⨅ i, (f i)⁻¹ := OrderIso.invENNReal.map_iSup _

lemma inv_sInf (s : Set ℝ≥0∞) : (sInf s)⁻¹ = ⨆ a ∈ s, a⁻¹ := by simp [sInf_eq_iInf, inv_iInf]

lemma inv_sSup (s : Set ℝ≥0∞) : (sSup s)⁻¹ = ⨅ a ∈ s, a⁻¹ := by simp [sSup_eq_iSup, inv_iSup]

lemma le_iInf_mul {ι : Type*} (u v : ι → ℝ≥0∞) :
    (⨅ i, u i) * ⨅ i, v i ≤ ⨅ i, u i * v i :=
  le_iInf fun i ↦ mul_le_mul' (iInf_le u i) (iInf_le v i)

lemma iSup_mul_le {ι : Type*} {u v : ι → ℝ≥0∞} :
    ⨆ i, u i * v i ≤ (⨆ i, u i) * ⨆ i, v i :=
  iSup_le fun i ↦ mul_le_mul' (le_iSup u i) (le_iSup v i)

lemma add_iSup [Nonempty ι] (f : ι → ℝ≥0∞) : a + ⨆ i, f i = ⨆ i, a + f i := by
  obtain rfl | ha := eq_or_ne a ∞
  · simp
  refine le_antisymm ?_ <| iSup_le fun i ↦ add_le_add_left (le_iSup ..) _
  refine add_le_of_le_tsub_left_of_le (le_iSup_of_le (Classical.arbitrary _) le_self_add) ?_
  exact iSup_le fun i ↦ ENNReal.le_sub_of_add_le_left ha <| le_iSup (a + f ·) i

lemma iSup_add [Nonempty ι] (f : ι → ℝ≥0∞) : (⨆ i, f i) + a = ⨆ i, f i + a := by
  simp [add_comm, add_iSup]

lemma add_biSup' {p : ι → Prop} (h : ∃ i, p i) (f : ι → ℝ≥0∞) :
    a + ⨆ i, ⨆ _ : p i, f i = ⨆ i, ⨆ _ : p i, a + f i := by
  haveI : Nonempty {i // p i} := nonempty_subtype.2 h
  simp only [iSup_subtype', add_iSup]

lemma biSup_add' {p : ι → Prop} (h : ∃ i, p i) (f : ι → ℝ≥0∞) :
    (⨆ i, ⨆ _ : p i, f i) + a = ⨆ i, ⨆ _ : p i, f i + a := by simp only [add_comm, add_biSup' h]

lemma add_biSup {ι : Type*} {s : Set ι} (hs : s.Nonempty) (f : ι → ℝ≥0∞) :
    a + ⨆ i ∈ s, f i = ⨆ i ∈ s, a + f i := add_biSup' hs _

lemma biSup_add {ι : Type*} {s : Set ι} (hs : s.Nonempty) (f : ι → ℝ≥0∞) :
    (⨆ i ∈ s, f i) + a = ⨆ i ∈ s, f i + a := biSup_add' hs _

lemma add_sSup (hs : s.Nonempty) : a + sSup s = ⨆ b ∈ s, a + b := by
  rw [sSup_eq_iSup, add_biSup hs]

lemma sSup_add (hs : s.Nonempty) : sSup s + a = ⨆ b ∈ s, b + a := by
  rw [sSup_eq_iSup, biSup_add hs]

lemma iSup_add_iSup_le [Nonempty ι] [Nonempty κ] {g : κ → ℝ≥0∞} (h : ∀ i j, f i + g j ≤ a) :
    iSup f + iSup g ≤ a := by simp_rw [iSup_add, add_iSup]; exact iSup₂_le h

lemma biSup_add_biSup_le' {p : ι → Prop} {q : κ → Prop} (hp : ∃ i, p i) (hq : ∃ j, q j)
    {g : κ → ℝ≥0∞} (h : ∀ i, p i → ∀ j, q j → f i + g j ≤ a) :
    (⨆ i, ⨆ _ : p i, f i) + ⨆ j, ⨆ _ : q j, g j ≤ a := by
  simp_rw [biSup_add' hp, add_biSup' hq]
  exact iSup₂_le fun i hi => iSup₂_le (h i hi)

lemma biSup_add_biSup_le {ι κ : Type*} {s : Set ι} {t : Set κ} (hs : s.Nonempty) (ht : t.Nonempty)
    {f : ι → ℝ≥0∞} {g : κ → ℝ≥0∞} {a : ℝ≥0∞} (h : ∀ i ∈ s, ∀ j ∈ t, f i + g j ≤ a) :
    (⨆ i ∈ s, f i) + ⨆ j ∈ t, g j ≤ a := biSup_add_biSup_le' hs ht h

lemma iSup_add_iSup (h : ∀ i j, ∃ k, f i + g j ≤ f k + g k) : iSup f + iSup g = ⨆ i, f i + g i := by
  cases isEmpty_or_nonempty ι
  · simp only [iSup_of_empty, bot_eq_zero, zero_add]
  · refine le_antisymm ?_ (iSup_le fun a => add_le_add (le_iSup _ _) (le_iSup _ _))
    refine iSup_add_iSup_le fun i j => ?_
    rcases h i j with ⟨k, hk⟩
    exact le_iSup_of_le k hk

lemma iSup_add_iSup_of_monotone {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] {f g : ι → ℝ≥0∞}
    (hf : Monotone f) (hg : Monotone g) : iSup f + iSup g = ⨆ a, f a + g a :=
  iSup_add_iSup fun i j ↦ (exists_ge_ge i j).imp fun _k ⟨hi, hj⟩ ↦ by gcongr <;> apply_rules

lemma finsetSum_iSup {α ι : Type*} {s : Finset α} {f : α → ι → ℝ≥0∞}
    (hf : ∀ i j, ∃ k, ∀ a, f a i ≤ f a k ∧ f a j ≤ f a k) :
    ∑ a ∈ s, ⨆ i, f a i = ⨆ i, ∑ a ∈ s, f a i := by
  induction' s using Finset.cons_induction with a s ha ihs
  · simp
  simp_rw [Finset.sum_cons, ihs]
  refine iSup_add_iSup fun i j ↦ (hf i j).imp fun k hk ↦ ?_
  gcongr
  exacts [(hk a).1, (hk _).2]

lemma finsetSum_iSup_of_monotone {α ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] {s : Finset α}
    {f : α → ι → ℝ≥0∞} (hf : ∀ a, Monotone (f a)) : (∑ a ∈ s, iSup (f a)) = ⨆ n, ∑ a ∈ s, f a n :=
  finsetSum_iSup fun i j ↦ (exists_ge_ge i j).imp fun _k ⟨hi, hj⟩ a ↦ ⟨hf a hi, hf a hj⟩

alias finset_sum_iSup_nat := finsetSum_iSup_of_monotone

lemma le_iInf_mul_iInf {g : κ → ℝ≥0∞} (hf : ∃ i, f i ≠ ∞) (hg : ∃ j, g j ≠ ∞)
    (ha : ∀ i j, a ≤ f i * g j) : a ≤ (⨅ i, f i) * ⨅ j, g j := by
  rw [← iInf_ne_top_subtype]
  have := nonempty_subtype.2 hf
  have := hg.nonempty
  replace hg : ⨅ j, g j ≠ ∞ := by simpa using hg
  rw [iInf_mul fun h ↦ (hg h).elim, le_iInf_iff]
  rintro ⟨i, hi⟩
  simpa [mul_iInf fun h ↦ (hi h).elim] using ha i

lemma iInf_mul_iInf {f g : ι → ℝ≥0∞} (hf : ∃ i, f i ≠ ∞) (hg : ∃ j, g j ≠ ∞)
    (h : ∀ i j, ∃ k, f k * g k ≤ f i * g j) : (⨅ i, f i) * ⨅ i, g i = ⨅ i, f i * g i := by
  refine le_antisymm (le_iInf fun i ↦ mul_le_mul' (iInf_le ..) (iInf_le ..))
    (le_iInf_mul_iInf hf hg fun i j ↦ ?_)
  obtain ⟨k, hk⟩ := h i j
  exact iInf_le_of_le k hk

lemma smul_iSup {R} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] (f : ι → ℝ≥0∞) (c : R) :
    c • ⨆ i, f i = ⨆ i, c • f i := by
  simp only [← smul_one_mul c (f _), ← smul_one_mul c (iSup _), ENNReal.mul_iSup]

lemma smul_sSup {R} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] (s : Set ℝ≥0∞) (c : R) :
    c • sSup s = ⨆ a ∈ s, c • a := by
  simp_rw [← smul_one_mul c (sSup s), ENNReal.mul_sSup, smul_one_mul]

lemma sub_iSup [Nonempty ι] (ha : a ≠ ∞) : a - ⨆ i, f i = ⨅ i, a - f i := by
  obtain ⟨i, hi⟩ | h := em (∃ i, a < f i)
  · rw [tsub_eq_zero_iff_le.2 <| le_iSup_of_le _ hi.le, (iInf_eq_bot _).2, bot_eq_zero]
    exact fun x hx ↦ ⟨i, by simpa [hi.le, tsub_eq_zero_of_le]⟩
  simp_rw [not_exists, not_lt] at h
  refine le_antisymm (le_iInf fun i ↦ tsub_le_tsub_left (le_iSup ..) _) <|
    ENNReal.le_sub_of_add_le_left (ne_top_of_le_ne_top ha <| iSup_le h) <|
    add_le_of_le_tsub_right_of_le (iInf_le_of_le (Classical.arbitrary _) tsub_le_self) <|
    iSup_le fun i ↦ ?_
  rw [← sub_sub_cancel ha (h _)]
  exact tsub_le_tsub_left (iInf_le (a - f ·) i) _

-- DISSOLVED: exists_lt_add_of_lt_add

end Inv

end ENNReal
