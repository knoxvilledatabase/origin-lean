/-
Extracted from Topology/MetricSpace/PiNat.lean
Genuine: 7 of 7 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Topological study of spaces `Π (n : ℕ), E n`

When `E n` are topological spaces, the space `Π (n : ℕ), E n` is naturally a topological space
(with the product topology). When `E n` are uniform spaces, it also inherits a uniform structure.
However, it does not inherit a canonical metric space structure of the `E n`. Nevertheless, one
can put a noncanonical metric space structure (or rather, several of them). This is done in this
file.

## Main definitions and results

One can define a combinatorial distance on `Π (n : ℕ), E n`, as follows:

* `PiNat.cylinder x n` is the set of points `y` with `x i = y i` for `i < n`.
* `PiNat.firstDiff x y` is the first index at which `x i ≠ y i`.
* `PiNat.dist x y` is equal to `(1/2) ^ (firstDiff x y)`. It defines a distance
  on `Π (n : ℕ), E n`, compatible with the topology when the `E n` have the discrete topology.
* `PiNat.metricSpace`: the metric space structure, given by this distance. Not registered as an
  instance. This space is a complete metric space.
* `PiNat.metricSpaceOfDiscreteUniformity`: the same metric space structure, but adjusting the
  uniformity defeqness when the `E n` already have the discrete uniformity. Not registered as an
  instance
* `PiNat.metricSpaceNatNat`: the particular case of `ℕ → ℕ`, not registered as an instance.

These results are used to construct continuous functions on `Π n, E n`:

* `PiNat.exists_retraction_of_isClosed`: given a nonempty closed subset `s` of `Π (n : ℕ), E n`,
  there exists a retraction onto `s`, i.e., a continuous map from the whole space to `s`
  restricting to the identity on `s`.
* `exists_nat_nat_continuous_surjective_of_completeSpace`: given any nonempty complete metric
  space with second-countable topology, there exists a continuous surjection from `ℕ → ℕ` onto
  this space.

One can also put distances on `Π (i : ι), E i` when the spaces `E i` are metric spaces (not discrete
in general), and `ι` is countable.

* `PiCountable.dist` is the distance on `Π i, E i` given by
    `dist x y = ∑' i, min (1/2)^(encode i) (dist (x i) (y i))`.
* `PiCountable.metricSpace` is the corresponding metric space structure, adjusted so that
  the uniformity is definitionally the product uniformity. Not registered as an instance.
* `PiNatEmbed` gives an equivalence between a space and itself in a sequence of spaces
* `Metric.PiNatEmbed.metricSpace` proves that a topological `X` separated by countably many
  continuous functions to metric spaces, can be embedded inside their product.

-/

noncomputable section

open Topology TopologicalSpace Set Metric Filter Function

attribute [local simp] pow_le_pow_iff_right₀ one_lt_two inv_le_inv₀ zero_le_two zero_lt_two

variable {E : ℕ → Type*}

namespace PiNat

/-! ### The firstDiff function -/

open Classical in

irreducible_def firstDiff (x y : ∀ n, E n) : ℕ :=
  if h : x ≠ y then Nat.find (ne_iff.1 h) else 0

theorem apply_firstDiff_ne {x y : ∀ n, E n} (h : x ≠ y) :
    x (firstDiff x y) ≠ y (firstDiff x y) := by
  rw [firstDiff_def, dif_pos h]
  classical
  exact Nat.find_spec (ne_iff.1 h)

theorem apply_eq_of_lt_firstDiff {x y : ∀ n, E n} {n : ℕ} (hn : n < firstDiff x y) : x n = y n := by
  rw [firstDiff_def] at hn
  split_ifs at hn with h
  · convert Nat.find_min (ne_iff.1 h) hn
    simp
  · exact (not_lt_zero' hn).elim

theorem firstDiff_comm (x y : ∀ n, E n) : firstDiff x y = firstDiff y x := by
  classical
  simp only [firstDiff_def, ne_comm]

theorem min_firstDiff_le (x y z : ∀ n, E n) (h : x ≠ z) :
    min (firstDiff x y) (firstDiff y z) ≤ firstDiff x z := by
  by_contra! H
  rw [lt_min_iff] at H
  refine apply_firstDiff_ne h ?_
  calc
    x (firstDiff x z) = y (firstDiff x z) := apply_eq_of_lt_firstDiff H.1
    _ = z (firstDiff x z) := apply_eq_of_lt_firstDiff H.2

/-! ### Cylinders -/

def cylinder (x : ∀ n, E n) (n : ℕ) : Set (∀ n, E n) :=
  { y | ∀ i, i < n → y i = x i }

theorem cylinder_eq_pi (x : ∀ n, E n) (n : ℕ) :
    cylinder x n = Set.pi (Finset.range n : Set ℕ) fun i : ℕ => {x i} := by
  ext y
  simp [cylinder]
