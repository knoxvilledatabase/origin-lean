/-
Extracted from Data/ENNReal/Operations.lean
Genuine: 92 of 129 | Dissolved: 27 | Infrastructure: 10
-/
import Origin.Core
import Mathlib.Algebra.BigOperators.WithTop
import Mathlib.Algebra.GroupWithZero.Divisibility
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.NNReal.Basic

/-!
# Properties of addition, multiplication and subtraction on extended non-negative real numbers

In this file we prove elementary properties of algebraic operations on `ℝ≥0∞`, including addition,
multiplication, natural powers and truncated subtraction, as well as how these interact with the
order structure on `ℝ≥0∞`. Notably excluded from this list are inversion and division, the
definitions and properties of which can be found in `Data.ENNReal.Inv`.

Note: the definitions of the operations included in this file can be found in `Data.ENNReal.Basic`.
-/

open Set NNReal ENNReal

namespace ENNReal

variable {a b c d : ℝ≥0∞} {r p q : ℝ≥0}

section Mul

@[mono, gcongr]
theorem mul_lt_mul (ac : a < c) (bd : b < d) : a * b < c * d := WithTop.mul_lt_mul ac bd

protected theorem mul_left_mono : Monotone (a * ·) := mul_left_mono

protected theorem mul_right_mono : Monotone (· * a) := mul_right_mono

-- DISSOLVED: pow_right_strictMono

-- DISSOLVED: pow_lt_pow_left

protected theorem max_mul : max a b * c = max (a * c) (b * c) := mul_right_mono.map_max

protected theorem mul_max : a * max b c = max (a * b) (a * c) := mul_left_mono.map_max

-- DISSOLVED: mul_left_strictMono

-- DISSOLVED: mul_lt_mul_left'

-- DISSOLVED: mul_lt_mul_right'

-- DISSOLVED: mul_eq_mul_left

-- DISSOLVED: mul_eq_mul_right

-- DISSOLVED: mul_le_mul_left

-- DISSOLVED: mul_le_mul_right

-- DISSOLVED: mul_lt_mul_left

-- DISSOLVED: mul_lt_mul_right

-- DISSOLVED: mul_eq_left

-- DISSOLVED: mul_eq_right

end Mul

section OperationsAndOrder

protected theorem pow_pos : 0 < a → ∀ n : ℕ, 0 < a ^ n :=
  CanonicallyOrderedCommSemiring.pow_pos

-- DISSOLVED: pow_ne_zero

theorem not_lt_zero : ¬a < 0 := by simp

protected theorem le_of_add_le_add_left : a ≠ ∞ → a + b ≤ a + c → b ≤ c :=
  WithTop.le_of_add_le_add_left

protected theorem le_of_add_le_add_right : a ≠ ∞ → b + a ≤ c + a → b ≤ c :=
  WithTop.le_of_add_le_add_right

@[gcongr] protected theorem add_lt_add_left : a ≠ ∞ → b < c → a + b < a + c :=
  WithTop.add_lt_add_left

@[gcongr] protected theorem add_lt_add_right : a ≠ ∞ → b < c → b + a < c + a :=
  WithTop.add_lt_add_right

protected theorem add_le_add_iff_left : a ≠ ∞ → (a + b ≤ a + c ↔ b ≤ c) :=
  WithTop.add_le_add_iff_left

protected theorem add_le_add_iff_right : a ≠ ∞ → (b + a ≤ c + a ↔ b ≤ c) :=
  WithTop.add_le_add_iff_right

protected theorem add_lt_add_iff_left : a ≠ ∞ → (a + b < a + c ↔ b < c) :=
  WithTop.add_lt_add_iff_left

protected theorem add_lt_add_iff_right : a ≠ ∞ → (b + a < c + a ↔ b < c) :=
  WithTop.add_lt_add_iff_right

protected theorem add_lt_add_of_le_of_lt : a ≠ ∞ → a ≤ b → c < d → a + c < b + d :=
  WithTop.add_lt_add_of_le_of_lt

protected theorem add_lt_add_of_lt_of_le : c ≠ ∞ → a < b → c ≤ d → a + c < b + d :=
  WithTop.add_lt_add_of_lt_of_le

instance addLeftReflectLT : AddLeftReflectLT ℝ≥0∞ :=
  WithTop.addLeftReflectLT

-- DISSOLVED: lt_add_right

end OperationsAndOrder

section OperationsAndInfty

variable {α : Type*}

@[simp] theorem add_eq_top : a + b = ∞ ↔ a = ∞ ∨ b = ∞ := WithTop.add_eq_top

@[simp] theorem add_lt_top : a + b < ∞ ↔ a < ∞ ∧ b < ∞ := WithTop.add_lt_top

theorem toNNReal_add {r₁ r₂ : ℝ≥0∞} (h₁ : r₁ ≠ ∞) (h₂ : r₂ ≠ ∞) :
    (r₁ + r₂).toNNReal = r₁.toNNReal + r₂.toNNReal := by
  lift r₁ to ℝ≥0 using h₁
  lift r₂ to ℝ≥0 using h₂
  rfl

theorem not_lt_top {x : ℝ≥0∞} : ¬x < ∞ ↔ x = ∞ := by rw [lt_top_iff_ne_top, Classical.not_not]

theorem add_ne_top : a + b ≠ ∞ ↔ a ≠ ∞ ∧ b ≠ ∞ := by simpa only [lt_top_iff_ne_top] using add_lt_top

@[aesop (rule_sets := [finiteness]) safe apply]
protected lemma Finiteness.add_ne_top {a b : ℝ≥0∞} (ha : a ≠ ∞) (hb : b ≠ ∞) : a + b ≠ ∞ :=
  ENNReal.add_ne_top.2 ⟨ha, hb⟩

theorem mul_top' : a * ∞ = if a = 0 then 0 else ∞ := by convert WithTop.mul_top' a

-- DISSOLVED: mul_top

theorem top_mul' : ∞ * a = if a = 0 then 0 else ∞ := by convert WithTop.top_mul' a

-- DISSOLVED: top_mul

theorem top_mul_top : ∞ * ∞ = ∞ := WithTop.top_mul_top

theorem top_pow {n : ℕ} (n_pos : 0 < n) : (∞ : ℝ≥0∞) ^ n = ∞ := WithTop.top_pow n_pos

-- DISSOLVED: mul_eq_top

theorem mul_lt_top : a < ∞ → b < ∞ → a * b < ∞ := WithTop.mul_lt_top

@[aesop (rule_sets := [finiteness]) unsafe 75% apply]
theorem mul_ne_top : a ≠ ∞ → b ≠ ∞ → a * b ≠ ∞ := WithTop.mul_ne_top

-- DISSOLVED: lt_top_of_mul_ne_top_left

-- DISSOLVED: lt_top_of_mul_ne_top_right

theorem mul_lt_top_iff {a b : ℝ≥0∞} : a * b < ∞ ↔ a < ∞ ∧ b < ∞ ∨ a = 0 ∨ b = 0 := by
  constructor
  · intro h
    rw [← or_assoc, or_iff_not_imp_right, or_iff_not_imp_right]
    intro hb ha
    exact ⟨lt_top_of_mul_ne_top_left h.ne hb, lt_top_of_mul_ne_top_right h.ne ha⟩
  · rintro (⟨ha, hb⟩ | rfl | rfl) <;> [exact mul_lt_top ha hb; simp; simp]

theorem mul_self_lt_top_iff {a : ℝ≥0∞} : a * a < ⊤ ↔ a < ⊤ := by
  rw [ENNReal.mul_lt_top_iff, and_self, or_self, or_iff_left_iff_imp]
  rintro rfl
  exact zero_lt_top

theorem mul_pos_iff : 0 < a * b ↔ 0 < a ∧ 0 < b :=
  CanonicallyOrderedCommSemiring.mul_pos

-- DISSOLVED: mul_pos

-- DISSOLVED: pow_eq_top_iff

theorem pow_eq_top (n : ℕ) (h : a ^ n = ∞) : a = ∞ :=
  (pow_eq_top_iff.1 h).1

theorem pow_ne_top (h : a ≠ ∞) {n : ℕ} : a ^ n ≠ ∞ :=
  mt (pow_eq_top n) h

theorem pow_lt_top : a < ∞ → ∀ n : ℕ, a ^ n < ∞ := by
  simpa only [lt_top_iff_ne_top] using pow_ne_top

@[simp, norm_cast]
theorem coe_finset_sum {s : Finset α} {f : α → ℝ≥0} : ↑(∑ a ∈ s, f a) = ∑ a ∈ s, (f a : ℝ≥0∞) :=
  map_sum ofNNRealHom f s

@[simp, norm_cast]
theorem coe_finset_prod {s : Finset α} {f : α → ℝ≥0} : ↑(∏ a ∈ s, f a) = ∏ a ∈ s, (f a : ℝ≥0∞) :=
  map_prod ofNNRealHom f s

end OperationsAndInfty

@[gcongr] protected theorem add_lt_add (ac : a < c) (bd : b < d) : a + b < c + d := by
  lift a to ℝ≥0 using ac.ne_top
  lift b to ℝ≥0 using bd.ne_top
  cases c; · simp
  cases d; · simp
  simp only [← coe_add, some_eq_coe, coe_lt_coe] at *
  exact add_lt_add ac bd

section Cancel

@[simp]
theorem addLECancellable_iff_ne {a : ℝ≥0∞} : AddLECancellable a ↔ a ≠ ∞ := by
  constructor
  · rintro h rfl
    refine zero_lt_one.not_le (h ?_)
    simp
  · rintro h b c hbc
    apply ENNReal.le_of_add_le_add_left h hbc

theorem cancel_of_ne {a : ℝ≥0∞} (h : a ≠ ∞) : AddLECancellable a :=
  addLECancellable_iff_ne.mpr h

theorem cancel_of_lt {a : ℝ≥0∞} (h : a < ∞) : AddLECancellable a :=
  cancel_of_ne h.ne

theorem cancel_of_lt' {a b : ℝ≥0∞} (h : a < b) : AddLECancellable a :=
  cancel_of_ne h.ne_top

theorem cancel_coe {a : ℝ≥0} : AddLECancellable (a : ℝ≥0∞) :=
  cancel_of_ne coe_ne_top

theorem add_right_inj (h : a ≠ ∞) : a + b = a + c ↔ b = c :=
  (cancel_of_ne h).inj

theorem add_left_inj (h : a ≠ ∞) : b + a = c + a ↔ b = c :=
  (cancel_of_ne h).inj_left

end Cancel

section Sub

theorem sub_eq_sInf {a b : ℝ≥0∞} : a - b = sInf { d | a ≤ d + b } :=
  le_antisymm (le_sInf fun _ h => tsub_le_iff_right.mpr h) <| sInf_le <| mem_setOf.2 le_tsub_add

@[simp, norm_cast] theorem coe_sub : (↑(r - p) : ℝ≥0∞) = ↑r - ↑p := WithTop.coe_sub

@[simp] theorem top_sub_coe : ∞ - ↑r = ∞ := WithTop.top_sub_coe

@[simp] lemma top_sub (ha : a ≠ ∞) : ∞ - a = ∞ := by lift a to ℝ≥0 using ha; exact top_sub_coe

theorem sub_top : a - ∞ = 0 := WithTop.sub_top

@[simp] theorem sub_eq_top_iff : a - b = ∞ ↔ a = ∞ ∧ b ≠ ∞ := WithTop.sub_eq_top_iff

lemma sub_ne_top_iff : a - b ≠ ∞ ↔ a ≠ ∞ ∨ b = ∞ := WithTop.sub_ne_top_iff

@[aesop (rule_sets := [finiteness]) unsafe 75% apply]
theorem sub_ne_top (ha : a ≠ ∞) : a - b ≠ ∞ := mt sub_eq_top_iff.mp <| mt And.left ha

@[simp, norm_cast]
theorem natCast_sub (m n : ℕ) : ↑(m - n) = (m - n : ℝ≥0∞) := by
  rw [← coe_natCast, Nat.cast_tsub, coe_sub, coe_natCast, coe_natCast]

alias nat_cast_sub := natCast_sub

protected theorem sub_eq_of_eq_add (hb : b ≠ ∞) : a = c + b → a - b = c :=
  (cancel_of_ne hb).tsub_eq_of_eq_add

protected lemma sub_eq_of_eq_add' (ha : a ≠ ∞) : a = c + b → a - b = c :=
  (cancel_of_ne ha).tsub_eq_of_eq_add'

protected theorem eq_sub_of_add_eq (hc : c ≠ ∞) : a + c = b → a = b - c :=
  (cancel_of_ne hc).eq_tsub_of_add_eq

protected lemma eq_sub_of_add_eq' (hb : b ≠ ∞) : a + c = b → a = b - c :=
  (cancel_of_ne hb).eq_tsub_of_add_eq'

protected theorem sub_eq_of_eq_add_rev (hb : b ≠ ∞) : a = b + c → a - b = c :=
  (cancel_of_ne hb).tsub_eq_of_eq_add_rev

protected lemma sub_eq_of_eq_add_rev' (ha : a ≠ ∞) : a = b + c → a - b = c :=
  (cancel_of_ne ha).tsub_eq_of_eq_add_rev'

theorem sub_eq_of_add_eq (hb : b ≠ ∞) (hc : a + b = c) : c - b = a :=
  ENNReal.sub_eq_of_eq_add hb hc.symm

@[simp]
protected theorem add_sub_cancel_left (ha : a ≠ ∞) : a + b - a = b :=
  (cancel_of_ne ha).add_tsub_cancel_left

@[simp]
protected theorem add_sub_cancel_right (hb : b ≠ ∞) : a + b - b = a :=
  (cancel_of_ne hb).add_tsub_cancel_right

protected theorem sub_add_eq_add_sub (hab : b ≤ a) (b_ne_top : b ≠ ∞) :
    a - b + c = a + c - b := by
  by_cases c_top : c = ∞
  · simpa [c_top] using ENNReal.eq_sub_of_add_eq b_ne_top rfl
  refine ENNReal.eq_sub_of_add_eq b_ne_top ?_
  simp only [add_assoc, add_comm c b]
  simpa only [← add_assoc] using (add_left_inj c_top).mpr <| tsub_add_cancel_of_le hab

protected theorem lt_add_of_sub_lt_left (h : a ≠ ∞ ∨ b ≠ ∞) : a - b < c → a < b + c := by
  obtain rfl | hb := eq_or_ne b ∞
  · rw [top_add, lt_top_iff_ne_top]
    exact fun _ => h.resolve_right (Classical.not_not.2 rfl)
  · exact (cancel_of_ne hb).lt_add_of_tsub_lt_left

protected theorem lt_add_of_sub_lt_right (h : a ≠ ∞ ∨ c ≠ ∞) : a - c < b → a < b + c :=
  add_comm c b ▸ ENNReal.lt_add_of_sub_lt_left h

theorem le_sub_of_add_le_left (ha : a ≠ ∞) : a + b ≤ c → b ≤ c - a :=
  (cancel_of_ne ha).le_tsub_of_add_le_left

theorem le_sub_of_add_le_right (hb : b ≠ ∞) : a + b ≤ c → a ≤ c - b :=
  (cancel_of_ne hb).le_tsub_of_add_le_right

protected theorem sub_lt_of_lt_add (hac : c ≤ a) (h : a < b + c) : a - c < b :=
  ((cancel_of_lt' <| hac.trans_lt h).tsub_lt_iff_right hac).mpr h

protected theorem sub_lt_iff_lt_right (hb : b ≠ ∞) (hab : b ≤ a) : a - b < c ↔ a < c + b :=
  (cancel_of_ne hb).tsub_lt_iff_right hab

-- DISSOLVED: sub_lt_self

protected theorem sub_lt_self_iff (ha : a ≠ ∞) : a - b < a ↔ 0 < a ∧ 0 < b :=
  (cancel_of_ne ha).tsub_lt_self_iff

theorem sub_lt_of_sub_lt (h₂ : c ≤ a) (h₃ : a ≠ ∞ ∨ b ≠ ∞) (h₁ : a - b < c) : a - c < b :=
  ENNReal.sub_lt_of_lt_add h₂ (add_comm c b ▸ ENNReal.lt_add_of_sub_lt_right h₃ h₁)

theorem sub_sub_cancel (h : a ≠ ∞) (h2 : b ≤ a) : a - (a - b) = b :=
  (cancel_of_ne <| sub_ne_top h).tsub_tsub_cancel_of_le h2

theorem sub_right_inj {a b c : ℝ≥0∞} (ha : a ≠ ∞) (hb : b ≤ a) (hc : c ≤ a) :
    a - b = a - c ↔ b = c :=
  (cancel_of_ne ha).tsub_right_inj (cancel_of_ne <| ne_top_of_le_ne_top ha hb)
    (cancel_of_ne <| ne_top_of_le_ne_top ha hc) hb hc

protected theorem sub_mul (h : 0 < b → b < a → c ≠ ∞) : (a - b) * c = a * c - b * c := by
  rcases le_or_lt a b with hab | hab; · simp [hab, mul_right_mono hab, tsub_eq_zero_of_le]
  rcases eq_or_lt_of_le (zero_le b) with (rfl | hb); · simp
  exact (cancel_of_ne <| mul_ne_top hab.ne_top (h hb hab)).tsub_mul

protected theorem mul_sub (h : 0 < c → c < b → a ≠ ∞) : a * (b - c) = a * b - a * c := by
  simp only [mul_comm a]
  exact ENNReal.sub_mul h

theorem sub_le_sub_iff_left (h : c ≤ a) (h' : a ≠ ∞) :
    (a - b ≤ a - c) ↔ c ≤ b :=
  (cancel_of_ne h').tsub_le_tsub_iff_left (cancel_of_ne (ne_top_of_le_ne_top h' h)) h

end Sub

section Sum

open Finset

variable {α : Type*} {s : Finset α} {f : α → ℝ≥0∞}

lemma prod_ne_top (h : ∀ a ∈ s, f a ≠ ∞) : ∏ a ∈ s, f a ≠ ∞ := WithTop.prod_ne_top h

lemma prod_lt_top (h : ∀ a ∈ s, f a < ∞) : ∏ a ∈ s, f a < ∞ := WithTop.prod_lt_top h

@[simp] lemma sum_eq_top : ∑ x ∈ s, f x = ∞ ↔ ∃ a ∈ s, f a = ∞ := WithTop.sum_eq_top

lemma sum_ne_top : ∑ a ∈ s, f a ≠ ∞ ↔ ∀ a ∈ s, f a ≠ ∞ := WithTop.sum_ne_top

@[simp] lemma sum_lt_top : ∑ a ∈ s, f a < ∞ ↔ ∀ a ∈ s, f a < ∞ := WithTop.sum_lt_top

theorem lt_top_of_sum_ne_top {s : Finset α} {f : α → ℝ≥0∞} (h : ∑ x ∈ s, f x ≠ ∞) {a : α}
    (ha : a ∈ s) : f a < ∞ :=
  sum_lt_top.1 h.lt_top a ha

theorem toNNReal_sum {s : Finset α} {f : α → ℝ≥0∞} (hf : ∀ a ∈ s, f a ≠ ∞) :
    ENNReal.toNNReal (∑ a ∈ s, f a) = ∑ a ∈ s, ENNReal.toNNReal (f a) := by
  rw [← coe_inj, coe_toNNReal, coe_finset_sum, sum_congr rfl]
  · intro x hx
    exact (coe_toNNReal (hf x hx)).symm
  · exact sum_ne_top.2 hf

theorem toReal_sum {s : Finset α} {f : α → ℝ≥0∞} (hf : ∀ a ∈ s, f a ≠ ∞) :
    ENNReal.toReal (∑ a ∈ s, f a) = ∑ a ∈ s, ENNReal.toReal (f a) := by
  rw [ENNReal.toReal, toNNReal_sum hf, NNReal.coe_sum]
  rfl

theorem ofReal_sum_of_nonneg {s : Finset α} {f : α → ℝ} (hf : ∀ i, i ∈ s → 0 ≤ f i) :
    ENNReal.ofReal (∑ i ∈ s, f i) = ∑ i ∈ s, ENNReal.ofReal (f i) := by
  simp_rw [ENNReal.ofReal, ← coe_finset_sum, coe_inj]
  exact Real.toNNReal_sum_of_nonneg hf

theorem sum_lt_sum_of_nonempty {s : Finset α} (hs : s.Nonempty) {f g : α → ℝ≥0∞}
    (Hlt : ∀ i ∈ s, f i < g i) : ∑ i ∈ s, f i < ∑ i ∈ s, g i := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton => simp [Hlt _ (Finset.mem_singleton_self _)]
  | cons _ _ _ _ ih =>
    simp only [Finset.sum_cons, forall_mem_cons] at Hlt ⊢
    exact ENNReal.add_lt_add Hlt.1 (ih Hlt.2)

theorem exists_le_of_sum_le {s : Finset α} (hs : s.Nonempty) {f g : α → ℝ≥0∞}
    (Hle : ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i) : ∃ i ∈ s, f i ≤ g i := by
  contrapose! Hle
  apply ENNReal.sum_lt_sum_of_nonempty hs Hle

end Sum

section Interval

variable {x y z : ℝ≥0∞} {ε ε₁ ε₂ : ℝ≥0∞} {s : Set ℝ≥0∞}

protected theorem Ico_eq_Iio : Ico 0 y = Iio y :=
  Ico_bot

-- DISSOLVED: mem_Iio_self_add

-- DISSOLVED: mem_Ioo_self_sub_add

end Interval

section Actions

noncomputable instance {M : Type*} [MulAction ℝ≥0∞ M] : MulAction ℝ≥0 M :=
  MulAction.compHom M ofNNRealHom.toMonoidHom

theorem smul_def {M : Type*} [MulAction ℝ≥0∞ M] (c : ℝ≥0) (x : M) : c • x = (c : ℝ≥0∞) • x :=
  rfl

instance {M N : Type*} [MulAction ℝ≥0∞ M] [MulAction ℝ≥0∞ N] [SMul M N] [IsScalarTower ℝ≥0∞ M N] :
    IsScalarTower ℝ≥0 M N where smul_assoc r := (smul_assoc (r : ℝ≥0∞) : _)

instance smulCommClass_left {M N : Type*} [MulAction ℝ≥0∞ N] [SMul M N] [SMulCommClass ℝ≥0∞ M N] :
    SMulCommClass ℝ≥0 M N where smul_comm r := (smul_comm (r : ℝ≥0∞) : _)

instance smulCommClass_right {M N : Type*} [MulAction ℝ≥0∞ N] [SMul M N] [SMulCommClass M ℝ≥0∞ N] :
    SMulCommClass M ℝ≥0 N where smul_comm m r := (smul_comm m (r : ℝ≥0∞) : _)

noncomputable instance {M : Type*} [AddMonoid M] [DistribMulAction ℝ≥0∞ M] :
    DistribMulAction ℝ≥0 M :=
  DistribMulAction.compHom M ofNNRealHom.toMonoidHom

noncomputable instance {M : Type*} [AddCommMonoid M] [Module ℝ≥0∞ M] : Module ℝ≥0 M :=
  Module.compHom M ofNNRealHom

noncomputable instance {A : Type*} [Semiring A] [Algebra ℝ≥0∞ A] : Algebra ℝ≥0 A where
  smul := (· • ·)
  commutes' r x := by simp [Algebra.commutes]
  smul_def' r x := by simp [← Algebra.smul_def (r : ℝ≥0∞) x, smul_def]
  toRingHom := (algebraMap ℝ≥0∞ A).comp (ofNNRealHom : ℝ≥0 →+* ℝ≥0∞)

noncomputable example : Algebra ℝ≥0 ℝ≥0∞ := inferInstance

noncomputable example : DistribMulAction ℝ≥0ˣ ℝ≥0∞ := inferInstance

theorem coe_smul {R} (r : R) (s : ℝ≥0) [SMul R ℝ≥0] [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0 ℝ≥0]
    [IsScalarTower R ℝ≥0 ℝ≥0∞] : (↑(r • s) : ℝ≥0∞) = (r : R) • (s : ℝ≥0∞) := by
  rw [← smul_one_smul ℝ≥0 r (s : ℝ≥0∞), smul_def, smul_eq_mul, ← ENNReal.coe_mul, smul_mul_assoc,
    one_mul]

theorem smul_top {R} [Zero R] [SMulWithZero R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    [NoZeroSMulDivisors R ℝ≥0∞] [DecidableEq R] (c : R) :
    c • ∞ = if c = 0 then 0 else ∞ := by
  rw [← smul_one_mul, mul_top']
  -- Porting note: need the primed version of `one_ne_zero` now
  simp_rw [smul_eq_zero, or_iff_left (one_ne_zero' ℝ≥0∞)]

lemma nnreal_smul_lt_top {x : ℝ≥0} {y : ℝ≥0∞} (hy : y < ⊤) : x • y < ⊤ := mul_lt_top (by simp) hy

lemma nnreal_smul_ne_top {x : ℝ≥0} {y : ℝ≥0∞} (hy : y ≠ ⊤) : x • y ≠ ⊤ := mul_ne_top (by simp) hy

-- DISSOLVED: nnreal_smul_ne_top_iff

-- DISSOLVED: nnreal_smul_lt_top_iff

end Actions

end ENNReal
