/-
Extracted from Analysis/Convex/Segment.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Segments in vector spaces

In a 𝕜-vector space, we define the following objects and properties.
* `segment 𝕜 x y`: Closed segment joining `x` and `y`.
* `openSegment 𝕜 x y`: Open segment joining `x` and `y`.

## Notation

We provide the following notation:
* `[x -[𝕜] y] = segment 𝕜 x y` in scope `Convex`

## TODO

Generalize all this file to affine spaces.

Should we rename `segment` and `openSegment` to `convex.Icc` and `convex.Ioo`? Should we also
define `clopenSegment`/`convex.Ico`/`convex.Ioc`?
-/

variable {𝕜 E F G ι : Type*} {M : ι → Type*}

open Function Module Set

open scoped Pointwise Convex

section OrderedSemiring

variable [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E]

section SMul

variable (𝕜) [SMul 𝕜 E] {s : Set E} {x y : E}

def segment (x y : E) : Set E :=
  { z : E | ∃ a b : 𝕜, 0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧ a • x + b • y = z }

def openSegment (x y : E) : Set E :=
  { z : E | ∃ a b : 𝕜, 0 < a ∧ 0 < b ∧ a + b = 1 ∧ a • x + b • y = z }
