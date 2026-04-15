/-
Extracted from Analysis/BoxIntegral/Box/Basic.lean
Genuine: 3 of 5 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Rectangular boxes in `ℝⁿ`

In this file we define rectangular boxes in `ℝⁿ`. As usual, we represent `ℝⁿ` as the type of
functions `ι → ℝ` (usually `ι = Fin n` for some `n`). When we need to interpret a box `[l, u]` as a
set, we use the product `{x | ∀ i, l i < x i ∧ x i ≤ u i}` of half-open intervals `(l i, u i]`. We
exclude `l i` because this way boxes of a partition are disjoint as sets in `ℝⁿ`.

Currently, the only use cases for these constructions are the definitions of Riemann-style integrals
(Riemann, Henstock-Kurzweil, McShane).

## Main definitions

We use the same structure `BoxIntegral.Box` both for ambient boxes and for elements of a partition.
Each box is stored as two points `lower upper : ι → ℝ` and a proof of `∀ i, lower i < upper i`. We
define instances `Membership (ι → ℝ) (Box ι)` and `CoeTC (Box ι) (Set <| ι → ℝ)` so that each box is
interpreted as the set `{x | ∀ i, x i ∈ Set.Ioc (I.lower i) (I.upper i)}`. This way boxes of a
partition are pairwise disjoint and their union is exactly the original box.

We require boxes to be nonempty, because this way coercion to sets is injective. The empty box can
be represented as `⊥ : WithBot (BoxIntegral.Box ι)`.

We define the following operations on boxes:

* coercion to `Set (ι → ℝ)` and `Membership (ι → ℝ) (BoxIntegral.Box ι)` as described above;
* `PartialOrder` and `SemilatticeSup` instances such that `I ≤ J` is equivalent to
  `(I : Set (ι → ℝ)) ⊆ J`;
* `Lattice` instances on `WithBot (BoxIntegral.Box ι)`;
* `BoxIntegral.Box.Icc`: the closed box `Set.Icc I.lower I.upper`; defined as a bundled monotone
  map from `Box ι` to `Set (ι → ℝ)`;
* `BoxIntegral.Box.face I i : Box (Fin n)`: a hyperface of `I : BoxIntegral.Box (Fin (n + 1))`;
* `BoxIntegral.Box.distortion`: the maximal ratio of two lengths of edges of a box; defined as the
  supremum of `nndist I.lower I.upper / nndist (I.lower i) (I.upper i)`.

We also provide a convenience constructor `BoxIntegral.Box.mk' (l u : ι → ℝ) : WithBot (Box ι)`
that returns the box `⟨l, u, _⟩` if it is nonempty and `⊥` otherwise.

## Tags

rectangular box
-/

open Set Function Metric Filter

noncomputable section

open scoped NNReal Topology

namespace BoxIntegral

variable {ι : Type*}

/-!
### Rectangular box: definition and partial order
-/

structure Box (ι : Type*) where
  /-- coordinates of the lower and upper corners of the box -/
  (lower upper : ι → ℝ)
  /-- Each lower coordinate is less than its upper coordinate: i.e., the box is non-empty -/
  lower_lt_upper : ∀ i, lower i < upper i

attribute [simp] Box.lower_lt_upper

namespace Box

variable (I J : Box ι) {x y : ι → ℝ}

-- INSTANCE (free from Core): :

theorem lower_le_upper : I.lower ≤ I.upper :=
  fun i ↦ (I.lower_lt_upper i).le

theorem lower_ne_upper (i) : I.lower i ≠ I.upper i :=
  (I.lower_lt_upper i).ne

-- INSTANCE (free from Core): :
