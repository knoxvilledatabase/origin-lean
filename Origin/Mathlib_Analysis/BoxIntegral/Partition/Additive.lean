/-
Extracted from Analysis/BoxIntegral/Partition/Additive.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Box additive functions

We say that a function `f : Box ι → M` from boxes in `ℝⁿ` to a commutative additive monoid `M` is
*box additive* on subboxes of `I₀ : WithTop (Box ι)` if for any box `J`, `↑J ≤ I₀`, and a partition
`π` of `J`, `f J = ∑ J' ∈ π.boxes, f J'`. We use `I₀ : WithTop (Box ι)` instead of `I₀ : Box ι` to
use the same definition for functions box additive on subboxes of a box and for functions box
additive on all boxes.

Examples of box-additive functions include the measure of a box and the integral of a fixed
integrable function over a box.

In this file we define box-additive functions and prove that a function such that
`f J = f (J ∩ {x | x i < y}) + f (J ∩ {x | y ≤ x i})` is box-additive.

## Tags

rectangular box, additive function
-/

noncomputable section

open Function Set

namespace BoxIntegral

variable {ι M : Type*} {n : ℕ}

structure BoxAdditiveMap (ι M : Type*) [AddCommMonoid M] (I : WithTop (Box ι)) where
  /-- The function underlying this additive map. -/
  toFun : Box ι → M
  sum_partition_boxes' : ∀ J : Box ι, ↑J ≤ I → ∀ π : Prepartition J, π.IsPartition →
    ∑ Ji ∈ π.boxes, toFun Ji = toFun J

scoped notation:25 ι " →ᵇᵃ " M => BoxIntegral.BoxAdditiveMap ι M ⊤
