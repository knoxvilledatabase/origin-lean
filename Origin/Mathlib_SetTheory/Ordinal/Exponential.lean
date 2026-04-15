/-
Extracted from SetTheory/Ordinal/Exponential.lean
Genuine: 49 of 75 | Dissolved: 24 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.SetTheory.Ordinal.Arithmetic

/-! # Ordinal exponential

In this file we define the power function and the logarithm function on ordinals. The two are
related by the lemma `Ordinal.opow_le_iff_le_log : b ^ c ≤ x ↔ c ≤ log b x` for nontrivial inputs
`b`, `c`.
-/

noncomputable section

open Function Set Equiv Order

open scoped Cardinal Ordinal

universe u v w

namespace Ordinal

instance pow : Pow Ordinal Ordinal :=
  ⟨fun a b => if a = 0 then 1 - b else limitRecOn b 1 (fun _ IH => IH * a) fun b _ => bsup.{u, u} b⟩

theorem opow_def (a b : Ordinal) :
    a ^ b = if a = 0 then 1 - b else limitRecOn b 1 (fun _ IH => IH * a) fun b _ => bsup.{u, u} b :=
  rfl

theorem zero_opow' (a : Ordinal) : 0 ^ a = 1 - a := by simp only [opow_def, if_true]

-- DISSOLVED: zero_opow

@[simp]
theorem opow_zero (a : Ordinal) : a ^ (0 : Ordinal) = 1 := by
  by_cases h : a = 0
  · simp only [opow_def, if_pos h, sub_zero]
  · simp only [opow_def, if_neg h, limitRecOn_zero]

@[simp]
theorem opow_succ (a b : Ordinal) : a ^ succ b = a ^ b * a :=
  if h : a = 0 then by subst a; simp only [zero_opow (succ_ne_zero _), mul_zero]
  else by simp only [opow_def, limitRecOn_succ, if_neg h]

-- DISSOLVED: opow_limit

-- DISSOLVED: opow_le_of_limit

-- DISSOLVED: lt_opow_of_limit

@[simp]
theorem opow_one (a : Ordinal) : a ^ (1 : Ordinal) = a := by
  rw [← succ_zero, opow_succ]; simp only [opow_zero, one_mul]

@[simp]
theorem one_opow (a : Ordinal) : (1 : Ordinal) ^ a = 1 := by
  induction a using limitRecOn with
  | H₁ => simp only [opow_zero]
  | H₂ _ ih =>
    simp only [opow_succ, ih, mul_one]
  | H₃ b l IH =>
    refine eq_of_forall_ge_iff fun c => ?_
    rw [opow_le_of_limit Ordinal.one_ne_zero l]
    exact ⟨fun H => by simpa only [opow_zero] using H 0 l.pos, fun H b' h => by rwa [IH _ h]⟩

theorem opow_pos {a : Ordinal} (b : Ordinal) (a0 : 0 < a) : 0 < a ^ b := by
  have h0 : 0 < a ^ (0 : Ordinal) := by simp only [opow_zero, zero_lt_one]
  induction b using limitRecOn with
  | H₁ => exact h0
  | H₂ b IH =>
    rw [opow_succ]
    exact mul_pos IH a0
  | H₃ b l _ =>
    exact (lt_opow_of_limit (Ordinal.pos_iff_ne_zero.1 a0) l).2 ⟨0, l.pos, h0⟩

-- DISSOLVED: opow_ne_zero

-- DISSOLVED: opow_eq_zero

@[simp, norm_cast]
theorem opow_natCast (a : Ordinal) (n : ℕ) : a ^ (n : Ordinal) = a ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, opow_zero, pow_zero]
  | succ n IH => rw [Nat.cast_succ, add_one_eq_succ, opow_succ, pow_succ, IH]

theorem isNormal_opow {a : Ordinal} (h : 1 < a) : IsNormal (a ^ ·) :=
  have a0 : 0 < a := zero_lt_one.trans h
  ⟨fun b => by simpa only [mul_one, opow_succ] using (mul_lt_mul_iff_left (opow_pos b a0)).2 h,
    fun _ l _ => opow_le_of_limit (ne_of_gt a0) l⟩

alias opow_isNormal := isNormal_opow

theorem opow_lt_opow_iff_right {a b c : Ordinal} (a1 : 1 < a) : a ^ b < a ^ c ↔ b < c :=
  (isNormal_opow a1).lt_iff

theorem opow_le_opow_iff_right {a b c : Ordinal} (a1 : 1 < a) : a ^ b ≤ a ^ c ↔ b ≤ c :=
  (isNormal_opow a1).le_iff

theorem opow_right_inj {a b c : Ordinal} (a1 : 1 < a) : a ^ b = a ^ c ↔ b = c :=
  (isNormal_opow a1).inj

theorem isLimit_opow {a b : Ordinal} (a1 : 1 < a) : IsLimit b → IsLimit (a ^ b) :=
  (isNormal_opow a1).isLimit

alias opow_isLimit := isLimit_opow

-- DISSOLVED: isLimit_opow_left

alias opow_isLimit_left := isLimit_opow_left

theorem opow_le_opow_right {a b c : Ordinal} (h₁ : 0 < a) (h₂ : b ≤ c) : a ^ b ≤ a ^ c := by
  rcases lt_or_eq_of_le (one_le_iff_pos.2 h₁) with h₁ | h₁
  · exact (opow_le_opow_iff_right h₁).2 h₂
  · subst a
    -- Porting note: `le_refl` is required.
    simp only [one_opow, le_refl]

theorem opow_le_opow_left {a b : Ordinal} (c : Ordinal) (ab : a ≤ b) : a ^ c ≤ b ^ c := by
  by_cases a0 : a = 0
  -- Porting note: `le_refl` is required.
  · subst a
    by_cases c0 : c = 0
    · subst c
      simp only [opow_zero, le_refl]
    · simp only [zero_opow c0, Ordinal.zero_le]
  · induction c using limitRecOn with
    | H₁ => simp only [opow_zero, le_refl]
    | H₂ c IH =>
      simpa only [opow_succ] using mul_le_mul' IH ab
    | H₃ c l IH =>
      exact
        (opow_le_of_limit a0 l).2 fun b' h =>
          (IH _ h).trans (opow_le_opow_right ((Ordinal.pos_iff_ne_zero.2 a0).trans_le ab) h.le)

theorem opow_le_opow {a b c d : Ordinal} (hac : a ≤ c) (hbd : b ≤ d) (hc : 0 < c) : a ^ b ≤ c ^ d :=
  (opow_le_opow_left b hac).trans (opow_le_opow_right hc hbd)

theorem left_le_opow (a : Ordinal) {b : Ordinal} (b1 : 0 < b) : a ≤ a ^ b := by
  nth_rw 1 [← opow_one a]
  cases' le_or_gt a 1 with a1 a1
  · rcases lt_or_eq_of_le a1 with a0 | a1
    · rw [lt_one_iff_zero] at a0
      rw [a0, zero_opow Ordinal.one_ne_zero]
      exact Ordinal.zero_le _
    rw [a1, one_opow, one_opow]
  rwa [opow_le_opow_iff_right a1, one_le_iff_pos]

theorem left_lt_opow {a b : Ordinal} (ha : 1 < a) (hb : 1 < b) : a < a ^ b := by
  conv_lhs => rw [← opow_one a]
  rwa [opow_lt_opow_iff_right ha]

theorem right_le_opow {a : Ordinal} (b : Ordinal) (a1 : 1 < a) : b ≤ a ^ b :=
  (isNormal_opow a1).le_apply

theorem opow_lt_opow_left_of_succ {a b c : Ordinal} (ab : a < b) : a ^ succ c < b ^ succ c := by
  rw [opow_succ, opow_succ]
  exact
    (mul_le_mul_right' (opow_le_opow_left c ab.le) a).trans_lt
      (mul_lt_mul_of_pos_left ab (opow_pos c ((Ordinal.zero_le a).trans_lt ab)))

theorem opow_add (a b c : Ordinal) : a ^ (b + c) = a ^ b * a ^ c := by
  rcases eq_or_ne a 0 with (rfl | a0)
  · rcases eq_or_ne c 0 with (rfl | c0)
    · simp
    have : b + c ≠ 0 := ((Ordinal.pos_iff_ne_zero.2 c0).trans_le (le_add_left _ _)).ne'
    simp only [zero_opow c0, zero_opow this, mul_zero]
  rcases eq_or_lt_of_le (one_le_iff_ne_zero.2 a0) with (rfl | a1)
  · simp only [one_opow, mul_one]
  induction c using limitRecOn with
  | H₁ => simp
  | H₂ c IH =>
    rw [add_succ, opow_succ, IH, opow_succ, mul_assoc]
  | H₃ c l IH =>
    refine
      eq_of_forall_ge_iff fun d =>
        (((isNormal_opow a1).trans (isNormal_add_right b)).limit_le l).trans ?_
    dsimp only [Function.comp_def]
    simp +contextual only [IH]
    exact
      (((isNormal_mul_right <| opow_pos b (Ordinal.pos_iff_ne_zero.2 a0)).trans
              (isNormal_opow a1)).limit_le
          l).symm

theorem opow_one_add (a b : Ordinal) : a ^ (1 + b) = a * a ^ b := by rw [opow_add, opow_one]

theorem opow_dvd_opow (a : Ordinal) {b c : Ordinal} (h : b ≤ c) : a ^ b ∣ a ^ c :=
  ⟨a ^ (c - b), by rw [← opow_add, Ordinal.add_sub_cancel_of_le h]⟩

theorem opow_dvd_opow_iff {a b c : Ordinal} (a1 : 1 < a) : a ^ b ∣ a ^ c ↔ b ≤ c :=
  ⟨fun h =>
    le_of_not_lt fun hn =>
      not_le_of_lt ((opow_lt_opow_iff_right a1).2 hn) <|
        le_of_dvd (opow_ne_zero _ <| one_le_iff_ne_zero.1 <| a1.le) h,
    opow_dvd_opow _⟩

theorem opow_mul (a b c : Ordinal) : a ^ (b * c) = (a ^ b) ^ c := by
  by_cases b0 : b = 0; · simp only [b0, zero_mul, opow_zero, one_opow]
  by_cases a0 : a = 0
  · subst a
    by_cases c0 : c = 0
    · simp only [c0, mul_zero, opow_zero]
    simp only [zero_opow b0, zero_opow c0, zero_opow (mul_ne_zero b0 c0)]
  cases' eq_or_lt_of_le (one_le_iff_ne_zero.2 a0) with a1 a1
  · subst a1
    simp only [one_opow]
  induction c using limitRecOn with
  | H₁ => simp only [mul_zero, opow_zero]
  | H₂ c IH =>
    rw [mul_succ, opow_add, IH, opow_succ]
  | H₃ c l IH =>
    refine
      eq_of_forall_ge_iff fun d =>
        (((isNormal_opow a1).trans (isNormal_mul_right (Ordinal.pos_iff_ne_zero.2 b0))).limit_le
              l).trans
          ?_
    dsimp only [Function.comp_def]
    simp +contextual only [IH]
    exact (opow_le_of_limit (opow_ne_zero _ a0) l).symm

-- DISSOLVED: opow_mul_add_pos

theorem opow_mul_add_lt_opow_mul_succ {b u w : Ordinal} (v : Ordinal) (hw : w < b ^ u) :
    b ^ u * v + w < b ^ u * succ v := by
  rwa [mul_succ, add_lt_add_iff_left]

theorem opow_mul_add_lt_opow_succ {b u v w : Ordinal} (hvb : v < b) (hw : w < b ^ u) :
    b ^ u * v + w < b ^ succ u := by
  convert (opow_mul_add_lt_opow_mul_succ v hw).trans_le
    (mul_le_mul_left' (succ_le_of_lt hvb) _) using 1
  exact opow_succ b u

/-! ### Ordinal logarithm -/

@[pp_nodot]
def log (b : Ordinal) (x : Ordinal) : Ordinal :=
  if 1 < b then pred (sInf { o | x < b ^ o }) else 0

private theorem log_nonempty {b x : Ordinal} (h : 1 < b) : { o : Ordinal | x < b ^ o }.Nonempty :=
  ⟨_, succ_le_iff.1 (right_le_opow _ h)⟩

theorem log_def {b : Ordinal} (h : 1 < b) (x : Ordinal) : log b x = pred (sInf { o | x < b ^ o }) :=
  if_pos h

theorem log_of_left_le_one {b : Ordinal} (h : b ≤ 1) (x : Ordinal) : log b x = 0 :=
  if_neg h.not_lt

theorem log_of_not_one_lt_left {b : Ordinal} (h : ¬1 < b) (x : Ordinal) : log b x = 0 := by
  simp only [log, if_neg h]

@[simp]
theorem log_zero_left : ∀ b, log 0 b = 0 :=
  log_of_left_le_one zero_le_one

@[simp]
theorem log_zero_right (b : Ordinal) : log b 0 = 0 := by
  obtain hb | hb := lt_or_le 1 b
  · rw [log_def hb, ← Ordinal.le_zero, pred_le, succ_zero]
    apply csInf_le'
    rw [mem_setOf, opow_one]
    exact bot_lt_of_lt hb
  · rw [log_of_left_le_one hb]

@[simp]
theorem log_one_left : ∀ b, log 1 b = 0 :=
  log_of_left_le_one le_rfl

-- DISSOLVED: succ_log_def

theorem lt_opow_succ_log_self {b : Ordinal} (hb : 1 < b) (x : Ordinal) :
    x < b ^ succ (log b x) := by
  rcases eq_or_ne x 0 with (rfl | hx)
  · apply opow_pos _ (zero_lt_one.trans hb)
  · rw [succ_log_def hb hx]
    exact csInf_mem (log_nonempty hb)

-- DISSOLVED: opow_log_le_self

-- DISSOLVED: opow_le_iff_le_log

-- DISSOLVED: opow_le_iff_le_log'

theorem le_log_of_opow_le {b x c : Ordinal} (hb : 1 < b) (h : b ^ c ≤ x) : c ≤ log b x := by
  obtain rfl | hx := eq_or_ne x 0
  · rw [Ordinal.le_zero, opow_eq_zero] at h
    exact (zero_lt_one.asymm <| h.1 ▸ hb).elim
  · exact (opow_le_iff_le_log hb hx).1 h

-- DISSOLVED: opow_le_of_le_log

-- DISSOLVED: lt_opow_iff_log_lt

-- DISSOLVED: lt_opow_iff_log_lt'

theorem lt_opow_of_log_lt {b x c : Ordinal} (hb : 1 < b) : log b x < c → x < b ^ c :=
  lt_imp_lt_of_le_imp_le <| le_log_of_opow_le hb

-- DISSOLVED: lt_log_of_lt_opow

-- DISSOLVED: log_pos

theorem log_eq_zero {b o : Ordinal} (hbo : o < b) : log b o = 0 := by
  rcases eq_or_ne o 0 with (rfl | ho)
  · exact log_zero_right b
  rcases le_or_lt b 1 with hb | hb
  · rcases le_one_iff.1 hb with (rfl | rfl)
    · exact log_zero_left o
    · exact log_one_left o
  · rwa [← Ordinal.le_zero, ← lt_succ_iff, succ_zero, ← lt_opow_iff_log_lt hb ho, opow_one]

@[mono]
theorem log_mono_right (b : Ordinal) {x y : Ordinal} (xy : x ≤ y) : log b x ≤ log b y := by
  obtain rfl | hx := eq_or_ne x 0
  · simp_rw [log_zero_right, Ordinal.zero_le]
  · obtain hb | hb := lt_or_le 1 b
    · exact (opow_le_iff_le_log hb (hx.bot_lt.trans_le xy).ne').1 <|
        (opow_log_le_self _ hx).trans xy
    · rw [log_of_left_le_one hb, log_of_left_le_one hb]

theorem log_le_self (b x : Ordinal) : log b x ≤ x := by
  obtain rfl | hx := eq_or_ne x 0
  · rw [log_zero_right]
  · obtain hb | hb := lt_or_le 1 b
    · exact (right_le_opow _ hb).trans (opow_log_le_self b hx)
    · simp_rw [log_of_left_le_one hb, Ordinal.zero_le]

@[simp]
theorem log_one_right (b : Ordinal) : log b 1 = 0 := by
  obtain hb | hb := lt_or_le 1 b
  · exact log_eq_zero hb
  · exact log_of_left_le_one hb 1

-- DISSOLVED: mod_opow_log_lt_self

theorem log_mod_opow_log_lt_log_self {b o : Ordinal} (hb : 1 < b) (hbo : b ≤ o) :
    log b (o % (b ^ log b o)) < log b o := by
  rcases eq_or_ne (o % (b ^ log b o)) 0 with h | h
  · rw [h, log_zero_right]
    exact log_pos hb (one_le_iff_ne_zero.1 (hb.le.trans hbo)) hbo
  · rw [← succ_le_iff, succ_log_def hb h]
    apply csInf_le'
    apply mod_lt
    rw [← Ordinal.pos_iff_ne_zero]
    exact opow_pos _ (zero_lt_one.trans hb)

-- DISSOLVED: log_eq_iff

-- DISSOLVED: log_opow_mul_add

-- DISSOLVED: log_opow_mul

theorem log_opow {b : Ordinal} (hb : 1 < b) (x : Ordinal) : log b (b ^ x) = x := by
  convert log_opow_mul hb x zero_ne_one.symm using 1
  · rw [mul_one]
  · rw [log_one_right, add_zero]

-- DISSOLVED: div_opow_log_pos

theorem div_opow_log_lt {b : Ordinal} (o : Ordinal) (hb : 1 < b) : o / (b ^ log b o) < b := by
  rw [div_lt (opow_pos _ (zero_lt_one.trans hb)).ne', ← opow_succ]
  exact lt_opow_succ_log_self hb o

-- DISSOLVED: add_log_le_log_mul

theorem omega0_opow_mul_nat_lt {a b : Ordinal} (h : a < b) (n : ℕ) : ω ^ a * n < ω ^ b := by
  apply lt_of_lt_of_le _ (opow_le_opow_right omega0_pos (succ_le_of_lt h))
  rw [opow_succ]
  exact mul_lt_mul_of_pos_left (nat_lt_omega0 n) (opow_pos a omega0_pos)

-- DISSOLVED: lt_omega0_opow

theorem lt_omega0_opow_succ {a b : Ordinal} : a < ω ^ succ b ↔ ∃ n : ℕ, a < ω ^ b * n := by
  refine ⟨fun ha ↦ ?_, fun ⟨n, hn⟩ ↦ hn.trans (omega0_opow_mul_nat_lt (lt_succ b) n)⟩
  obtain ⟨c, hc, n, hn⟩ := (lt_omega0_opow (succ_ne_zero b)).1 ha
  refine ⟨n, hn.trans_le (mul_le_mul_right' ?_ _)⟩
  rwa [opow_le_opow_iff_right one_lt_omega0, ← lt_succ_iff]

/-! ### Interaction with `Nat.cast` -/

@[simp, norm_cast]
theorem natCast_opow (m : ℕ) : ∀ n : ℕ, ↑(m ^ n : ℕ) = (m : Ordinal) ^ (n : Ordinal)
  | 0 => by simp
  | n + 1 => by
    rw [pow_succ, natCast_mul, natCast_opow m n, Nat.cast_succ, add_one_eq_succ, opow_succ]

theorem iSup_pow {o : Ordinal} (ho : 0 < o) : ⨆ n : ℕ, o ^ n = o ^ ω := by
  simp_rw [← opow_natCast]
  rcases (one_le_iff_pos.2 ho).lt_or_eq with ho₁ | rfl
  · exact (isNormal_opow ho₁).apply_omega0
  · rw [one_opow]
    refine le_antisymm (Ordinal.iSup_le fun n => by rw [one_opow]) ?_
    exact_mod_cast Ordinal.le_iSup _ 0

set_option linter.deprecated false in

theorem sup_opow_nat {o : Ordinal} (ho : 0 < o) : (sup fun n : ℕ => o ^ n) = o ^ ω := by
  simp_rw [← opow_natCast]
  rcases (one_le_iff_pos.2 ho).lt_or_eq with ho₁ | rfl
  · exact (isNormal_opow ho₁).apply_omega0
  · rw [one_opow]
    refine le_antisymm (sup_le fun n => by rw [one_opow]) ?_
    convert le_sup (fun n : ℕ => 1 ^ (n : Ordinal)) 0
    rw [Nat.cast_zero, opow_zero]

end Ordinal
