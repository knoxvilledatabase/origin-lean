/-
Extracted from NumberTheory/Padics/MahlerBasis.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# The Mahler basis of continuous functions

In this file we introduce the Mahler basis function `mahler k`, for `k : ℕ`, which is the unique
continuous map `ℤ_[p] → ℤ_[p]` agreeing with `n ↦ n.choose k` for `n ∈ ℕ`.

Using this, we prove Mahler's theorem, showing that for any continuous function `f` on `ℤ_[p]`
(valued in a normed `ℤ_[p]`-module `E`), the Mahler series `x ↦ ∑' k, mahler k x • Δ^[n] f 0`
converges (uniformly) to `f`, and this construction defines a Banach-space isomorphism between
`C(ℤ_[p], E)` and the space of sequences `ℕ → E` tending to 0.

For this, we follow the argument of Bojanić [bojanic74].

The formalisation of Mahler's theorem presented here is based on code written by Giulio Caflisch
for his bachelor's thesis at ETH Zürich.

## References

* [R. Bojanić, *A simple proof of Mahler's theorem on approximation of continuous functions of a
  p-adic variable by polynomials*][bojanic74]
* [P. Colmez, *Fonctions d'une variable p-adique*][colmez2010]

## Tags

Bojanic
-/

open Finset IsUltrametricDist NNReal Filter

open scoped fwdDiff ZeroAtInfty Topology

variable {p : ℕ} [hp : Fact p.Prime]

namespace PadicInt

lemma norm_ascPochhammer_le (k : ℕ) (x : ℤ_[p]) :
    ‖(ascPochhammer ℤ_[p] k).eval x‖ ≤ ‖(k.factorial : ℤ_[p])‖ := by
  let f := (ascPochhammer ℤ_[p] k).eval
  change ‖f x‖ ≤ ‖_‖
  have hC : (k.factorial : ℤ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hf : ContinuousAt f x := Polynomial.continuousAt _
  -- find `n : ℕ` such that `‖f x - f n‖ ≤ ‖k!‖`
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ‖f x - f n‖ ≤ ‖(k.factorial : ℤ_[p])‖ := by
    obtain ⟨δ, hδp, hδ⟩ := Metric.continuousAt_iff.mp hf _ (norm_pos_iff.mpr hC)
    obtain ⟨n, hn'⟩ := PadicInt.denseRange_natCast.exists_dist_lt x hδp
    simpa only [← dist_eq_norm_sub'] using ⟨n, (hδ (dist_comm x n ▸ hn')).le⟩
  -- use ultrametric property to show that `‖f n‖ ≤ ‖k!‖` implies `‖f x‖ ≤ ‖k!‖`
  refine sub_add_cancel (f x) _ ▸ (IsUltrametricDist.norm_add_le_max _ (f n)).trans (max_le hn ?_)
  -- finish using the fact that `n.multichoose k ∈ ℤ`
  simp_rw [f, ← ascPochhammer_eval_cast, Polynomial.eval_eq_smeval,
    ← Ring.factorial_nsmul_multichoose_eq_ascPochhammer, smul_eq_mul, Nat.cast_mul, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (norm_le_one _)

-- INSTANCE (free from Core): :

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): instBinomialRing
