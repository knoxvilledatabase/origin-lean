/-
Extracted from Analysis/Analytic/Composition.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Composition of analytic functions

In this file we prove that the composition of analytic functions is analytic.

The argument is the following. Assume `g z = ∑' qₙ (z, ..., z)` and `f y = ∑' pₖ (y, ..., y)`. Then

`g (f y) = ∑' qₙ (∑' pₖ (y, ..., y), ..., ∑' pₖ (y, ..., y))
= ∑' qₙ (p_{i₁} (y, ..., y), ..., p_{iₙ} (y, ..., y))`.

For each `n` and `i₁, ..., iₙ`, define a `i₁ + ... + iₙ` multilinear function mapping
`(y₀, ..., y_{i₁ + ... + iₙ - 1})` to
`qₙ (p_{i₁} (y₀, ..., y_{i₁-1}), p_{i₂} (y_{i₁}, ..., y_{i₁ + i₂ - 1}), ..., p_{iₙ} (....)))`.
Then `g ∘ f` is obtained by summing all these multilinear functions.

To formalize this, we use compositions of an integer `N`, i.e., its decompositions into
a sum `i₁ + ... + iₙ` of positive integers. Given such a composition `c` and two formal
multilinear series `q` and `p`, let `q.compAlongComposition p c` be the above multilinear
function. Then the `N`-th coefficient in the power series expansion of `g ∘ f` is the sum of these
terms over all `c : Composition N`.

To complete the proof, we need to show that this power series has a positive radius of convergence.
This follows from the fact that `Composition N` has cardinality `2^(N-1)` and estimates on
the norm of `qₙ` and `pₖ`, which give summability. We also need to show that it indeed converges to
`g ∘ f`. For this, we note that the composition of partial sums converges to `g ∘ f`, and that it
corresponds to a part of the whole sum, on a subset that increases to the whole space. By
summability of the norms, this implies the overall convergence.

## Main results

* `q.comp p` is the formal composition of the formal multilinear series `q` and `p`.
* `HasFPowerSeriesAt.comp` states that if two functions `g` and `f` admit power series expansions
  `q` and `p`, then `g ∘ f` admits a power series expansion given by `q.comp p`.
* `AnalyticAt.comp` states that the composition of analytic functions is analytic.
* `FormalMultilinearSeries.comp_assoc` states that composition is associative on formal
  multilinear series.

## Implementation details

The main technical difficulty is to write down things. In particular, we need to define precisely
`q.compAlongComposition p c` and to show that it is indeed a continuous multilinear
function. This requires a whole interface built on the class `Composition`. Once this is set,
the main difficulty is to reorder the sums, writing the composition of the partial sums as a sum
over some subset of `Σ n, Composition n`. We need to check that the reordering is a bijection,
running over difficulties due to the dependent nature of the types under consideration, that are
controlled thanks to the interface for `Composition`.

The associativity of composition on formal multilinear series is a nontrivial result: it does not
follow from the associativity of composition of analytic functions, as there is no uniqueness for
the formal multilinear series representing a function (and also, it holds even when the radius of
convergence of the series is `0`). Instead, we give a direct proof, which amounts to reordering
double sums in a careful way. The change of variables is a canonical (combinatorial) bijection
`Composition.sigmaEquivSigmaPi` between `(Σ (a : Composition n), Composition a.length)` and
`(Σ (c : Composition n), Π (i : Fin c.length), Composition (c.blocksFun i))`, and is described
in more details below in the paragraph on associativity.
-/

noncomputable section

variable {𝕜 : Type*} {E F G H : Type*}

open Filter List

open scoped Topology NNReal ENNReal

section Topological

variable [CommRing 𝕜] [AddCommGroup E] [AddCommGroup F] [AddCommGroup G]

variable [Module 𝕜 E] [Module 𝕜 F] [Module 𝕜 G]

variable [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace G]

/-! ### Composing formal multilinear series -/

namespace FormalMultilinearSeries

variable [IsTopologicalAddGroup E] [ContinuousConstSMul 𝕜 E]

variable [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜 F]

variable [IsTopologicalAddGroup G] [ContinuousConstSMul 𝕜 G]

/-!
In this paragraph, we define the composition of formal multilinear series, by summing over all
possible compositions of `n`.
-/

def applyComposition (p : FormalMultilinearSeries 𝕜 E F) {n : ℕ} (c : Composition n) :
    (Fin n → E) → Fin c.length → F := fun v i => p (c.blocksFun i) (v ∘ c.embedding i)

theorem applyComposition_ones (p : FormalMultilinearSeries 𝕜 E F) (n : ℕ) :
    p.applyComposition (Composition.ones n) = fun v i =>
      p 1 fun _ => v (Fin.castLE (Composition.length_le _) i) := by
  funext v i
  apply p.congr (Composition.ones_blocksFun _ _)
  intro j hjn hj1
  obtain rfl : j = 0 := by lia
  refine congr_arg v ?_
  rw [Fin.ext_iff, Fin.val_castLE, Composition.ones_embedding, Fin.val_mk]

set_option backward.isDefEq.respectTransparency false in

theorem applyComposition_single (p : FormalMultilinearSeries 𝕜 E F) {n : ℕ} (hn : 0 < n)
    (v : Fin n → E) : p.applyComposition (Composition.single n hn) v = fun _j => p n v := by
  ext j
  refine p.congr (by simp) fun i hi1 hi2 => ?_
  dsimp
  congr 1
  convert Composition.single_embedding hn ⟨i, hi2⟩ using 1
  obtain ⟨j_val, j_property⟩ := j
  have : j_val = 0 := le_bot_iff.1 (Nat.lt_succ_iff.1 j_property)
  congr!
  simp
