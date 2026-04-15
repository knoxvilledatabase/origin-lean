/-
Extracted from Analysis/RCLike/Lemmas.lean
Genuine: 6 of 9 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-! # Further lemmas about `RCLike` -/

open scoped Finset

variable {K E : Type*} [RCLike K]

open ComplexOrder RCLike in

lemma convex_RCLike_iff_convex_real [AddCommMonoid E] [Module K E] [Module ℝ E]
    [IsScalarTower ℝ K E] {s : Set E} : Convex K s ↔ Convex ℝ s :=
  ⟨Convex.lift ℝ,
  fun hs => convex_of_nonneg_surjective_algebraMap _ (fun _ => nonneg_iff_exists_ofReal.mp) hs⟩

namespace Polynomial

theorem ofReal_eval (p : ℝ[X]) (x : ℝ) : (↑(p.eval x) : K) = aeval (↑x) p :=
  (@aeval_algebraMap_apply_eq_algebraMap_eval ℝ K _ _ _ x p).symm

end Polynomial

variable (K) in

lemma RCLike.span_one_I : Submodule.span ℝ (M := K) {1, I} = ⊤ := by
  suffices ∀ x : K, ∃ a b : ℝ, a • 1 + b • I = x by
    simpa [Submodule.eq_top_iff', Submodule.mem_span_pair]
  exact fun x ↦ ⟨re x, im x, by simp [real_smul_eq_coe_mul]⟩

variable (K) in

lemma RCLike.rank_le_two : Module.rank ℝ K ≤ 2 :=
  calc
    _ = Module.rank ℝ ↥(Submodule.span ℝ ({1, I} : Set K)) := by rw [span_one_I]; simp
    _ ≤ #({1, I} : Finset K) := by
      -- TODO: `simp` doesn't rewrite inside the type argument to `Module.rank`, but `rw` does.
      -- We should introduce `Submodule.rank` to fix this.
      have := rank_span_finset_le (R := ℝ) (M := K) {1, I}
      rw [Finset.coe_pair] at this
      simpa [span_one_I] using this
    _ ≤ 2 := mod_cast Finset.card_le_two

variable (K) in

lemma RCLike.finrank_le_two : Module.finrank ℝ K ≤ 2 :=
  Module.finrank_le_of_rank_le <| rank_le_two _

namespace FiniteDimensional

open RCLike

library_note «RCLike instance» /--

-- INSTANCE (free from Core): generates

`RCLike ?m`. Since this can only be satisfied by `ℝ` or `ℂ`, this does not cause problems. -/

-- INSTANCE (free from Core): rclike_to_real

variable (K E)

variable [NormedAddCommGroup E] [NormedSpace K E]

theorem proper_rclike [FiniteDimensional K E] : ProperSpace E := by
  -- Using `have` not `let` since it is only existence of `NormedSpace` structure that we need.
  have : NormedSpace ℝ E := .restrictScalars ℝ K E
  have : FiniteDimensional ℝ E := FiniteDimensional.trans ℝ K E
  infer_instance

variable {E}

-- INSTANCE (free from Core): RCLike.properSpace_submodule

end FiniteDimensional

namespace RCLike
