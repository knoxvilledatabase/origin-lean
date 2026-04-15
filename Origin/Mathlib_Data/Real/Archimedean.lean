/-
Extracted from Data/Real/Archimedean.lean
Genuine: 2 of 4 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# The real numbers are an Archimedean floor ring, and a conditionally complete linear order.

-/

assert_not_exists Finset

open Pointwise CauSeq

namespace Real

variable {ι : Sort*} {f : ι → ℝ} {s : Set ℝ} {a : ℝ}

-- INSTANCE (free from Core): instArchimedean

-- INSTANCE (free from Core): :

theorem isCauSeq_iff_lift {f : ℕ → ℚ} : IsCauSeq abs f ↔ IsCauSeq abs fun i => (f i : ℝ) where
  mp H ε ε0 :=
    let ⟨δ, δ0, δε⟩ := exists_pos_rat_lt ε0
    (H _ δ0).imp fun i hi j ij => by dsimp; exact lt_trans (mod_cast hi _ ij) δε
  mpr H ε ε0 :=
    (H _ (Rat.cast_pos.2 ε0)).imp fun i hi j ij => by dsimp at hi; exact mod_cast hi _ ij

theorem of_near (f : ℕ → ℚ) (x : ℝ) (h : ∀ ε > 0, ∃ i, ∀ j ≥ i, |(f j : ℝ) - x| < ε) :
    ∃ h', Real.mk ⟨f, h'⟩ = x :=
  ⟨isCauSeq_iff_lift.2 (CauSeq.of_near _ (const abs x) h),
    sub_eq_zero.1 <|
      abs_eq_zero.1 <|
        (eq_of_le_of_forall_lt_imp_le_of_dense (abs_nonneg _)) fun _ε ε0 =>
          mk_near_of_forall_near <| (h _ ε0).imp fun _i h j ij => le_of_lt (h j ij)⟩
