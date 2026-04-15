/-
Extracted from Analysis/Calculus/LineDeriv/Basic.lean
Genuine: 12 of 12 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Line derivatives

We define the line derivative of a function `f : E → F`, at a point `x : E` along a vector `v : E`,
as the element `f' : F` such that `f (x + t • v) = f x + t • f' + o (t)` as `t` tends to `0` in
the scalar field `𝕜`, if it exists. It is denoted by `lineDeriv 𝕜 f x v`.

This notion is generally less well behaved than the full Fréchet derivative (for instance, the
composition of functions which are line-differentiable is not line-differentiable in general).
The Fréchet derivative should therefore be favored over this one in general, although the line
derivative may sometimes prove handy.

The line derivative in direction `v` is also called the Gateaux derivative in direction `v`,
although the term "Gateaux derivative" is sometimes reserved for the situation where there is
such a derivative in all directions, for the map `v ↦ lineDeriv 𝕜 f x v` (which doesn't have to be
linear in general).

## Main definition and results

We mimic the definitions and statements for the Fréchet derivative and the one-dimensional
derivative. We define in particular the following objects:

* `LineDifferentiableWithinAt 𝕜 f s x v`
* `LineDifferentiableAt 𝕜 f x v`
* `HasLineDerivWithinAt 𝕜 f f' s x v`
* `HasLineDerivAt 𝕜 f s x v`
* `lineDerivWithin 𝕜 f s x v`
* `lineDeriv 𝕜 f x v`

and develop about them a basic API inspired by the one for the Fréchet derivative.

We depart from the Fréchet derivative in two places, as the dependence of the following predicates
on the direction would make them barely usable:
* We do not define an analogue of the predicate `UniqueDiffOn`;
* We do not define `LineDifferentiableOn` nor `LineDifferentiable`.
-/

noncomputable section

open scoped Topology Filter ENNReal NNReal

open Filter Asymptotics Set

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

section Module

/-!
Results that do not rely on a topological structure on `E`
-/

variable (𝕜)

variable {E : Type*} [AddCommGroup E] [Module 𝕜 E]

def HasLineDerivWithinAt (f : E → F) (f' : F) (s : Set E) (x : E) (v : E) :=
  HasDerivWithinAt (fun t ↦ f (x + t • v)) f' ((fun t ↦ x + t • v) ⁻¹' s) (0 : 𝕜)

def HasLineDerivAt (f : E → F) (f' : F) (x : E) (v : E) :=
  HasDerivAt (fun t ↦ f (x + t • v)) f' (0 : 𝕜)

def LineDifferentiableWithinAt (f : E → F) (s : Set E) (x : E) (v : E) : Prop :=
  DifferentiableWithinAt 𝕜 (fun t ↦ f (x + t • v)) ((fun t ↦ x + t • v) ⁻¹' s) (0 : 𝕜)

def LineDifferentiableAt (f : E → F) (x : E) (v : E) : Prop :=
  DifferentiableAt 𝕜 (fun t ↦ f (x + t • v)) (0 : 𝕜)

def lineDerivWithin (f : E → F) (s : Set E) (x : E) (v : E) : F :=
  derivWithin (fun t ↦ f (x + t • v)) ((fun t ↦ x + t • v) ⁻¹' s) (0 : 𝕜)

def lineDeriv (f : E → F) (x : E) (v : E) : F :=
  deriv (fun t ↦ f (x + t • v)) (0 : 𝕜)

variable {𝕜}

variable {f f₁ : E → F} {f' f₀' f₁' : F} {s t : Set E} {x v : E}

lemma HasLineDerivWithinAt.mono (hf : HasLineDerivWithinAt 𝕜 f f' s x v) (hst : t ⊆ s) :
    HasLineDerivWithinAt 𝕜 f f' t x v :=
  HasDerivWithinAt.mono hf (preimage_mono hst)

lemma HasLineDerivAt.hasLineDerivWithinAt (hf : HasLineDerivAt 𝕜 f f' x v) (s : Set E) :
    HasLineDerivWithinAt 𝕜 f f' s x v :=
  HasDerivAt.hasDerivWithinAt hf

lemma HasLineDerivWithinAt.lineDifferentiableWithinAt (hf : HasLineDerivWithinAt 𝕜 f f' s x v) :
    LineDifferentiableWithinAt 𝕜 f s x v :=
  HasDerivWithinAt.differentiableWithinAt hf

theorem HasLineDerivAt.lineDifferentiableAt (hf : HasLineDerivAt 𝕜 f f' x v) :
    LineDifferentiableAt 𝕜 f x v :=
  HasDerivAt.differentiableAt hf

theorem LineDifferentiableWithinAt.hasLineDerivWithinAt (h : LineDifferentiableWithinAt 𝕜 f s x v) :
    HasLineDerivWithinAt 𝕜 f (lineDerivWithin 𝕜 f s x v) s x v :=
  DifferentiableWithinAt.hasDerivWithinAt h

theorem LineDifferentiableAt.hasLineDerivAt (h : LineDifferentiableAt 𝕜 f x v) :
    HasLineDerivAt 𝕜 f (lineDeriv 𝕜 f x v) x v :=
  DifferentiableAt.hasDerivAt h
