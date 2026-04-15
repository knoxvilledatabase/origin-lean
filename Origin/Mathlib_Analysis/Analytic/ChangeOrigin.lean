/-
Extracted from Analysis/Analytic/ChangeOrigin.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Changing origin in a power series

If a function is analytic in a disk `D(x, R)`, then it is analytic in any disk contained in that
one. Indeed, one can write
$$
f (x + y + z) = \sum_{n} p_n (y + z)^n = \sum_{n, k} \binom{n}{k} p_n y^{n-k} z^k
= \sum_{k} \Bigl(\sum_{n} \binom{n}{k} p_n y^{n-k}\Bigr) z^k.
$$
The corresponding power series has thus a `k`-th coefficient equal to
$\sum_{n} \binom{n}{k} p_n y^{n-k}$. In the general case where `pₙ` is a multilinear map, this has
to be interpreted suitably: instead of having a binomial coefficient, one should sum over all
possible subsets `s` of `Fin n` of cardinality `k`, and attribute `z` to the indices in `s` and
`y` to the indices outside of `s`.

In this file, we implement this. The new power series is called `p.changeOrigin y`. Then, we
check its convergence and the fact that its sum coincides with the original sum. The outcome of this
discussion is that the set of points where a function is analytic is open. All these arguments
require the target space to be complete, as otherwise the series might not converge.

### Main results

In a complete space, if a function admits a power series in a ball, then it is analytic at any
point `y` of this ball, and the power series there can be expressed in terms of the initial power
series `p` as `p.changeOrigin y`. See `HasFPowerSeriesOnBall.changeOrigin`. It follows in particular
that the set of points at which a given function is analytic is open, see `isOpen_analyticAt`.
-/

noncomputable section

open scoped NNReal ENNReal Topology

open Filter Set

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

[NormedAddCommGroup F] [NormedSpace 𝕜 F]

namespace FormalMultilinearSeries

variable (p : FormalMultilinearSeries 𝕜 E F) {x y : E} {r : ℝ≥0}

def changeOriginSeriesTerm (k l : ℕ) (s : Finset (Fin (k + l))) (hs : s.card = l) :
    E [×l]→L[𝕜] E [×k]→L[𝕜] F :=
  let a := ContinuousMultilinearMap.curryFinFinset 𝕜 E F hs
    (by rw [Finset.card_compl, Fintype.card_fin, hs, add_tsub_cancel_right])
  a (p (k + l))

theorem changeOriginSeriesTerm_apply (k l : ℕ) (s : Finset (Fin (k + l))) (hs : s.card = l)
    (x y : E) :
    (p.changeOriginSeriesTerm k l s hs (fun _ => x) fun _ => y) =
      p (k + l) (s.piecewise (fun _ => x) fun _ => y) :=
  ContinuousMultilinearMap.curryFinFinset_apply_const _ _ _ _ _
