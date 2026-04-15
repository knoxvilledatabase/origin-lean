/-
Extracted from Topology/EMetricSpace/Lipschitz.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Lipschitz continuous functions

A map `f : α → β` between two (extended) metric spaces is called *Lipschitz continuous*
with constant `K ≥ 0` if for all `x, y` we have `edist (f x) (f y) ≤ K * edist x y`.
For a metric space, the latter inequality is equivalent to `dist (f x) (f y) ≤ K * dist x y`.
There is also a version asserting this inequality only for `x` and `y` in some set `s`.
Finally, `f : α → β` is called *locally Lipschitz continuous* if each `x : α` has a neighbourhood
on which `f` is Lipschitz continuous (with some constant).

In this file we provide various ways to prove that various combinations of Lipschitz continuous
functions are Lipschitz continuous. We also prove that Lipschitz continuous functions are
uniformly continuous, and that locally Lipschitz functions are continuous.

## Main definitions and lemmas

* `LipschitzWith K f`: states that `f` is Lipschitz with constant `K : ℝ≥0`
* `LipschitzOnWith K f s`: states that `f` is Lipschitz with constant `K : ℝ≥0` on a set `s`
* `LipschitzWith.uniformContinuous`: a Lipschitz function is uniformly continuous
* `LipschitzOnWith.uniformContinuousOn`: a function which is Lipschitz on a set `s` is uniformly
  continuous on `s`.
* `LocallyLipschitz f`: states that `f` is locally Lipschitz
* `LocallyLipschitzOn f s`: states that `f` is locally Lipschitz on `s`.
* `LocallyLipschitz.continuous`: a locally Lipschitz function is continuous.


## Implementation notes

The parameter `K` has type `ℝ≥0`. This way we avoid conjunction in the definition and have
coercions both to `ℝ` and `ℝ≥0∞`. Constructors whose names end with `'` take `K : ℝ` as an
argument, and return `LipschitzWith (Real.toNNReal K) f`.
-/

universe u v w x

open Filter Function Set Topology NNReal ENNReal Bornology

variable {α : Type u} {β : Type v} {γ : Type w} {ι : Type x}

section PseudoEMetricSpace

variable [PseudoEMetricSpace α] [PseudoEMetricSpace β] {K : ℝ≥0} {s t : Set α} {f : α → β}

def LipschitzWith (K : ℝ≥0) (f : α → β) := ∀ x y, edist (f x) (f y) ≤ K * edist x y

def LipschitzOnWith (K : ℝ≥0) (f : α → β) (s : Set α) :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → edist (f x) (f y) ≤ K * edist x y

def LocallyLipschitz (f : α → β) : Prop := ∀ x, ∃ K, ∃ t ∈ 𝓝 x, LipschitzOnWith K f t

def LocallyLipschitzOn (s : Set α) (f : α → β) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∃ K, ∃ t ∈ 𝓝[s] x, LipschitzOnWith K f t
