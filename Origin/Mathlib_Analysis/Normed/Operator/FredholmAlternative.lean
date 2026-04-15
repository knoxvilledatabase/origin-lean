/-
Extracted from Analysis/Normed/Operator/FredholmAlternative.lean
Genuine: 1 of 4 | Dissolved: 3 | Infrastructure: 0
-/
import Origin.Core

/-!
# Spectral theory of compact operators

This file develops the spectral theory of compact operators on Banach spaces.
The main result is the Fredholm alternative for compact operators.

## Main results

* `antilipschitz_of_not_hasEigenvalue`: if `T` is a compact operator and `μ ≠ 0` is not an
  eigenvalue, then `T - μI` is antilipschitz, i.e. bounded below.
* `hasEigenvalue_or_mem_resolventSet`: the Fredholm alternative for compact operators, which says
  that if `T` is a compact operator and `μ ≠ 0`, then either `μ` is an eigenvalue of `T`, or `μ`
  is in the resolvent set of `T`.
* `hasEigenvalue_iff_mem_spectrum`: if `T` is a compact operator, then the nonzero eigenvalues of
  `T` are exactly the nonzero points in the spectrum of `T`.

We follow the proof given in Section 2 of
https://terrytao.wordpress.com/2011/04/10/a-proof-of-the-fredholm-alternative/
but adapt it to work in a more general setting of spaces over nontrivially normed fields,
rather than just over `ℝ` or `ℂ`. The main technical hurdle is that we don't have the ability to
rescale vectors to have norm exactly `1`, so we have to work with vectors in a shell instead of on
the unit sphere, and this makes some of the intermediate statements more complicated.
-/

namespace IsCompactOperator

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

variable {T : X →L[𝕜] X} {μ : 𝕜}

open Module End

open Filter Topology in

-- DISSOLVED: antilipschitz_of_not_hasEigenvalue

set_option backward.isDefEq.respectTransparency false in

private theorem exists_seq {S : End 𝕜 X} (hS_not_surj : ¬ (S : X → X).Surjective)
    (hS_anti : Topology.IsClosedEmbedding S)
    {c : 𝕜} (hc : 1 < ‖c‖) {R : ℝ} (hR : ‖c‖ < R) :
    ∃ f : ℕ → X,
      (∀ n, 1 ≤ ‖f n‖) ∧ (∀ n, ‖f n‖ ≤ R) ∧ (∀ n, f n ∈ (S ^ n).range) ∧
      (∀ n, ∀ y ∈ (S ^ (n + 1)).range, 1 ≤ ‖f n - y‖) := by
  -- Construct the sequence of submodules `V n := (S ^ n).range`, and show that they are closed.
  let V (n : ℕ) : Submodule 𝕜 X := S.iterateRange n
  have hV_succ (n : ℕ) : V (n + 1) = (V n).map (S : End 𝕜 X) := LinearMap.iterateRange_succ
  have hV_closed (n : ℕ) : IsClosed (V n : Set X) := by
    induction n with
    | zero => simp [V, Module.End.one_eq_id]
    | succ n ih =>
      rw [hV_succ]
      apply hS_anti.isClosedMap _ ih
  -- Apply Riesz's lemma repeatedly using the closed subspace `V (n+1)` inside `V n`.
  have x (n : ℕ) : ∃ x ∈ V n, 1 ≤ ‖x‖ ∧ ‖x‖ ≤ R ∧ ∀ y ∈ V (n + 1), 1 ≤ ‖x - y‖ := by
    have h₁ : IsClosed ((V (n + 1)).comap (V n).subtype : Set (V n)) := by
      simpa using (hV_closed (n + 1)).preimage_val
    have h₂ : ∃ x : V n, x ∉ (V (n + 1)).comap (V n).subtype := by
      simpa [iterate_succ, V, (iterate_injective hS_anti.injective n).eq_iff,
        Function.Surjective] using hS_not_surj
    obtain ⟨⟨x, hx⟩, hxn, hxy⟩ := riesz_lemma_of_norm_lt hc hR h₁ h₂
    simp only [Submodule.mem_comap, Submodule.subtype_apply, AddSubgroupClass.coe_norm,
      AddSubgroupClass.coe_sub, Subtype.forall] at hxn hxy
    exact ⟨x, hx, by simpa using hxy 0, hxn,
      fun y hy ↦ hxy y (S.iterateRange.monotone (by simp) hy) hy⟩
  -- Use the existential claim to construct the sequence `f n`.
  choose x hxv hxn hxn' hxy using x
  exact ⟨x, hxn, hxn', hxv, hxy⟩

variable [CompleteSpace X]

-- DISSOLVED: hasEigenvalue_or_mem_resolventSet

-- DISSOLVED: hasEigenvalue_iff_mem_spectrum

end IsCompactOperator
