/-
Extracted from Analysis/Calculus/ContDiff/Comp.lean
Genuine: 3 of 5 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Higher differentiability of composition

We prove that the composition of `C^n` functions is `C^n`.
We also expand the API around `C^n` functions.

## Main results

* `ContDiff.comp` states that the composition of two `C^n` functions is `C^n`.

Similar results are given for `C^n` functions on domains.

## Notation

We use the notation `E [×n]→L[𝕜] F` for the space of continuous multilinear maps on `E^n` with
values in `F`. This is the space in which the `n`-th derivative of a function from `E` to `F` lives.

In this file, we denote `(⊤ : ℕ∞) : WithTop ℕ∞` with `∞` and `⊤ : WithTop ℕ∞` with `ω`.

## Tags

derivative, differentiability, higher derivative, `C^n`, multilinear, Taylor series, formal series
-/

public noncomputable section

open Set Filter Function

open scoped Topology ContDiff

-- INSTANCE (free from Core): 1001]

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] {s t : Set E} {f : E → F}
  {g : F → G} {x x₀ : E} {m n : WithTop ℕ∞}

section comp

/-!
### Composition of `C^n` functions

We show that the composition of `C^n` functions is `C^n`. One way to do this would be to
use the following simple inductive proof. Assume it is done for `n`.
Then, to check it for `n+1`, one needs to check that the derivative of `g ∘ f` is `C^n`, i.e.,
that `Dg(f x) ⬝ Df(x)` is `C^n`. The term `Dg (f x)` is the composition of two `C^n` functions, so
it is `C^n` by the inductive assumption. The term `Df(x)` is also `C^n`. Then, the matrix
multiplication is the application of a bilinear map (which is `C^∞`, and therefore `C^n`) to
`x ↦ (Dg(f x), Df x)`. As the composition of two `C^n` maps, it is again `C^n`, and we are done.

There are two difficulties in this proof.

The first one is that it is an induction over all Banach
spaces. In Lean, this is only possible if they belong to a fixed universe. One could formalize this
by first proving the statement in this case, and then extending the result to general universes
by embedding all the spaces we consider in a common universe through `ULift`.

The second one is that it does not work cleanly for analytic maps: for this case, we need to
exhibit a whole sequence of derivatives which are all analytic, not just finitely many of them, so
an induction is never enough at a finite step.

Both these difficulties can be overcome with some cost. However, we choose a different path: we
write down an explicit formula for the `n`-th derivative of `g ∘ f` in terms of derivatives of
`g` and `f` (this is the formula of Faa-Di Bruno) and use this formula to get a suitable Taylor
expansion for `g ∘ f`. Writing down the formula of Faa-Di Bruno is not easy as the formula is quite
intricate, but it is also useful for other purposes and once available it makes the proof here
essentially trivial.
-/

theorem ContDiffOn.comp {s : Set E} {t : Set F} {g : F → G} {f : E → F} (hg : ContDiffOn 𝕜 n g t)
    (hf : ContDiffOn 𝕜 n f s) (st : MapsTo f s t) : ContDiffOn 𝕜 n (g ∘ f) s :=
  fun x hx ↦ ContDiffWithinAt.comp x (hg (f x) (st hx)) (hf x hx) st

theorem ContDiffOn.comp_inter
    {s : Set E} {t : Set F} {g : F → G} {f : E → F} (hg : ContDiffOn 𝕜 n g t)
    (hf : ContDiffOn 𝕜 n f s) : ContDiffOn 𝕜 n (g ∘ f) (s ∩ f ⁻¹' t) :=
  hg.comp (hf.mono inter_subset_left) inter_subset_right

theorem ContDiff.comp_contDiffOn {s : Set E} {g : F → G} {f : E → F} (hg : ContDiff 𝕜 n g)
    (hf : ContDiffOn 𝕜 n f s) : ContDiffOn 𝕜 n (g ∘ f) s :=
  (contDiffOn_univ.2 hg).comp hf (mapsTo_univ _ _)
