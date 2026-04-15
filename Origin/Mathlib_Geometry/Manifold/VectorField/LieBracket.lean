/-
Extracted from Geometry/Manifold/VectorField/LieBracket.lean
Genuine: 3 of 5 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Lie brackets of vector fields on manifolds

We define the Lie bracket of two vector fields, denoted with
`VectorField.mlieBracket I V W x`, as the pullback in the manifold of the corresponding notion
in the model space (through `extChartAt I x`).

The main results are the following:
* `VectorField.mpullback_mlieBracket` states that the pullback of the Lie bracket
  is the Lie bracket of the pullbacks.
* `VectorField.leibniz_identity_mlieBracket` is the Leibniz (or Jacobi)
  identity `[U, [V, W]] = [[U, V], W] + [V, [U, W]]`.

-/

open Set Function Filter NormedSpace

open scoped Topology Manifold ContDiff

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {H : Type*} [TopologicalSpace H] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {H' : Type*} [TopologicalSpace H'] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {H'' : Type*} [TopologicalSpace H''] {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {I'' : ModelWithCorners 𝕜 E'' H''}
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M'']
  {f : M → M'} {s t : Set M} {x x₀ : M}

namespace VectorField

section LieBracket

/-! ### The Lie bracket of vector fields in manifolds -/

variable {V W V₁ W₁ : Π (x : M), TangentSpace I x}

variable (I I') in

def mlieBracketWithin (V W : Π (x : M), TangentSpace I x) (s : Set M) (x₀ : M) :
    TangentSpace I x₀ :=
  mpullback I 𝓘(𝕜, E) (extChartAt I x₀)
    (lieBracketWithin 𝕜
      (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm V (range I))
      (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm W (range I))
      ((extChartAt I x₀).symm ⁻¹' s ∩ range I)) x₀

variable (I I') in

def mlieBracket (V W : Π (x : M), TangentSpace I x) (x₀ : M) : TangentSpace I x₀ :=
  mlieBracketWithin I V W univ x₀

set_option backward.isDefEq.respectTransparency false in

lemma mlieBracketWithin_eq_lieBracketWithin {V W : Π (x : E), TangentSpace 𝓘(𝕜, E) x} {s : Set E} :
    mlieBracketWithin 𝓘(𝕜, E) V W s = lieBracketWithin 𝕜 V W s := by
  ext x
  simp [mlieBracketWithin_apply]
