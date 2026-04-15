/-
Extracted from Data/Nat/Order/Lemmas.lean
Genuine: 2 of 5 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Further lemmas about the natural numbers

The distinction between this file and `Mathlib/Algebra/Order/Ring/Nat.lean` is not particularly
clear. They were separated for now to minimize the porting requirements for tactics
during the transition to mathlib4. Please feel free to reorganize these two files.
-/

assert_not_exists RelIso

namespace Nat

/-! ### Sets -/

-- INSTANCE (free from Core): Subtype.orderBot

-- INSTANCE (free from Core): Subtype.semilatticeSup

theorem set_eq_univ {S : Set ℕ} : S = Set.univ ↔ 0 ∈ S ∧ ∀ k : ℕ, k ∈ S → k + 1 ∈ S :=
  ⟨by rintro rfl; simp, fun ⟨h0, hs⟩ => Set.eq_univ_of_forall (set_induction h0 hs)⟩

lemma exists_not_and_succ_of_not_zero_of_exists {p : ℕ → Prop} (H' : ¬ p 0) (H : ∃ n, p n) :
    ∃ n, ¬ p n ∧ p (n + 1) := by
  classical
  let k := Nat.find H
  have hk : p k := Nat.find_spec H
  suffices 0 < k from
    ⟨k - 1, Nat.find_min H <| Nat.pred_lt this.ne', by rwa [Nat.sub_add_cancel this]⟩
  by_contra! contra
  rw [le_zero_eq] at contra
  exact H' (contra ▸ hk)

end Nat
