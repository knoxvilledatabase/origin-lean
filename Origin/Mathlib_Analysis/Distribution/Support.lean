/-
Extracted from Analysis/Distribution/Support.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Support of distributions

We define the support of a distribution, `dsupport u`, as the intersection of all closed sets for
which `u` vanishes on the complement.
For this we also define a predicate `IsVanishingOn` that asserts that a map `f : F → V` vanishes on
`s : Set α` if for all `u : F` with `tsupport u ⊆ s` it follows that `f u = 0`.

These definitions work independently of a specific class of distributions (classical, tempered, or
compactly supported) and all basic properties are proved in an abstract setting using `FunLike`.

## Main definitions
* `IsVanishingOn`: A distribution vanishes on a set if it acts trivially on all test functions
  supported in that subset.
* `dsupport`: The support of a distribution is the intersection of all closed sets for which that
  distribution vanishes on the complement of the set.

## Main statements
* `TemperedDistribution.dsupport_delta`: The support of the delta distribution is a single point.

-/

variable {ι α β 𝕜 E F F₁ F₂ R V : Type*}

open scoped Topology

namespace Distribution

section IsVanishingOn

variable [FunLike F α β] [TopologicalSpace α] [Zero β]

variable {f g : F → V} {s s₁ s₂ : Set α}

/-! ### Vanishing of distributions -/

section Zero

variable [Zero V]

def IsVanishingOn (f : F → V) (s : Set α) : Prop :=
    ∀ (u : F), tsupport u ⊆ s → f u = 0
