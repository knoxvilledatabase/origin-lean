/-
Extracted from SetTheory/Cardinal/Arithmetic.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Cardinal arithmetic

Arithmetic operations on cardinals are defined in `Mathlib/SetTheory/Cardinal/Order.lean`. However,
proving the important theorem `c * c = c` for infinite cardinals and its corollaries requires the
use of ordinal numbers. This is done within this file.

## Main statements

* `Cardinal.mul_eq_max` and `Cardinal.add_eq_max` state that the product (resp. sum) of two infinite
  cardinals is just their maximum. Several variations around this fact are also given.
* `Cardinal.mk_list_eq_mk`: when `α` is infinite, `α` and `List α` have the same cardinality.

## Tags

cardinal arithmetic (for infinite cardinals)
-/

assert_not_exists Module Finsupp Ordinal.log

noncomputable section

open Function Set Cardinal Equiv Order Ordinal

universe u v w

namespace Cardinal

/-! ### Properties of `mul` -/

section mul

theorem mul_eq_self {c : Cardinal} (hc : ℵ₀ ≤ c) : c * c = c := by
  -- The only nontrivial part is `c * c ≤ c`. We prove it inductively.
  induction c using WellFoundedLT.induction with | ind c IH
  refine le_antisymm ?_ (by simpa using mul_le_mul_right (one_le_aleph0.trans hc) c)
  -- Consider the minimal well-order on `α` (a type with cardinality `c`).
  induction c using Cardinal.inductionOn with | mk α
  obtain ⟨_, _, hα⟩ := exists_ord_eq_type_lt α
  have : NoMaxOrder α := by
    rw [← isSuccPrelimit_type_lt_iff, ← hα]
    exact (isSuccLimit_ord hc).isSuccPrelimit
  -- Define an order `s` on `α × α`, comparing first by `max x.1 x.2`, then by `toLex (x.1, x.2)`.
  let g : α × α → α := uncurry max
  let f : α × α ↪ α ×ₗ (α ×ₗ α) := ⟨fun p ↦ toLex (g p, toLex p), fun p q ↦ congrArg Prod.snd⟩
  let s := f ⁻¹'o (· < ·)
  have : IsWellOrder _ s := (RelEmbedding.preimage ..).isWellOrder
  -- Every initial segment of `s` is contained in `β × β` for some `β` of cardinality `< c`.
  -- By the inductive hypothesis, this means `#(β × β) < c`. Thus, `α × α` must have
  -- cardinality `≤ c`.
  refine @card_le_card (type s) (typeLT α) <| le_of_forall_lt fun o h ↦ ?_
  obtain ⟨p, rfl⟩ := typein_surj s h
  obtain ⟨q, hq'⟩ := exists_gt (g p)
  rw [← hα, lt_ord]
  apply lt_of_le_of_lt (b := #(Iio q) * #(Iio q))
  · apply (Set.embeddingOfSubset { x | s x p } ..).cardinal_le.trans_eq (mk_setProd ..)
    simp [s, f, Prod.Lex.lt_iff, subset_def]
    grind
  rcases lt_or_ge #(Iio q) ℵ₀ with hq | hq
  · exact (mul_lt_aleph0 hq hq).trans_le hc
  · have := mk_Iio_lt q hα
    rwa [IH _ this hq]

theorem mul_eq_max {a b : Cardinal} (ha : ℵ₀ ≤ a) (hb : ℵ₀ ≤ b) : a * b = max a b :=
  le_antisymm
      (mul_eq_self (ha.trans (le_max_left a b)) ▸
        mul_le_mul' (le_max_left _ _) (le_max_right _ _)) <|
    max_le (by simpa only [mul_one] using mul_le_mul_right (one_le_aleph0.trans hb) a)
      (by simpa only [one_mul] using mul_le_mul_left (one_le_aleph0.trans ha) b)
