/-
Extracted from Geometry/Manifold/MFDeriv/FDeriv.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
### Relations between vector space derivative and manifold derivative

The manifold derivative `mfderiv`, when considered on the model vector space with its trivial
manifold structure, coincides with the usual Fréchet derivative `fderiv`. In this section, we prove
this and related statements.
-/

noncomputable section

open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {f : E → E'}
  {s : Set E} {x : E}

section MFDerivFDeriv

theorem uniqueMDiffWithinAt_iff_uniqueDiffWithinAt :
    UniqueMDiffWithinAt 𝓘(𝕜, E) s x ↔ UniqueDiffWithinAt 𝕜 s x := by
  simp only [UniqueMDiffWithinAt, mfld_simps]

alias ⟨UniqueMDiffWithinAt.uniqueDiffWithinAt, UniqueDiffWithinAt.uniqueMDiffWithinAt⟩ :=

  uniqueMDiffWithinAt_iff_uniqueDiffWithinAt

theorem uniqueMDiffOn_iff_uniqueDiffOn : UniqueMDiffOn 𝓘(𝕜, E) s ↔ UniqueDiffOn 𝕜 s := by
  simp [UniqueMDiffOn, UniqueDiffOn, uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]

alias ⟨UniqueMDiffOn.uniqueDiffOn, UniqueDiffOn.uniqueMDiffOn⟩ := uniqueMDiffOn_iff_uniqueDiffOn

theorem ModelWithCorners.uniqueMDiffOn {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) : UniqueMDiffOn 𝓘(𝕜, E) (Set.range I) :=
  I.uniqueDiffOn.uniqueMDiffOn

#adaptation_note /-- After https://github.com/leanprover/lean4/pull/12179

the simpNF linter complains about this being `@[simp]`. -/
