/-
Extracted from Analysis/Subadditive.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Convergence of subadditive sequences

A subadditive sequence `u : ℕ → ℝ` is a sequence satisfying `u (m + n) ≤ u m + u n` for all `m, n`.
We define this notion as `Subadditive u`, and prove in `Subadditive.tendsto_lim` that, if `u n / n`
is bounded below, then it converges to a limit (that we denote by `Subadditive.lim` for
convenience). This result is known as Fekete's lemma in the literature.

## TODO

Define a bundled `SubadditiveHom`, use it.
-/

noncomputable section

open Set Filter Topology

def Subadditive (u : ℕ → ℝ) : Prop :=
  ∀ m n, u (m + n) ≤ u m + u n

namespace Subadditive

variable {u : ℕ → ℝ} (h : Subadditive u)
