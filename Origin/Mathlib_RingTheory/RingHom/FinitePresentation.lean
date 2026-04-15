/-
Extracted from RingTheory/RingHom/FinitePresentation.lean
Genuine: 7 of 7 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# The meta properties of finitely-presented ring homomorphisms.

The main result is `RingHom.finitePresentation_isLocal`.

-/

open scoped Pointwise TensorProduct

namespace RingHom

theorem finitePresentation_stableUnderComposition : StableUnderComposition @FinitePresentation := by
  introv R hf hg
  exact hg.comp hf

theorem finitePresentation_respectsIso : RingHom.RespectsIso @RingHom.FinitePresentation :=
  finitePresentation_stableUnderComposition.respectsIso
    fun e ↦ .of_surjective _ e.surjective <| by simpa using Submodule.fg_bot

theorem finitePresentation_isStableUnderBaseChange :
    IsStableUnderBaseChange @FinitePresentation := by
  apply IsStableUnderBaseChange.mk
  · exact finitePresentation_respectsIso
  · simp only [finitePresentation_algebraMap]
    intros
    infer_instance

theorem finitePresentation_localizationPreserves : LocalizationPreserves @FinitePresentation :=
  finitePresentation_isStableUnderBaseChange.localizationPreserves

theorem finitePresentation_holdsForLocalizationAway :
    HoldsForLocalizationAway @FinitePresentation := by
  introv R _
  rw [finitePresentation_algebraMap]
  exact IsLocalization.Away.finitePresentation r

theorem finitePresentation_ofLocalizationSpanTarget :
    OfLocalizationSpanTarget @FinitePresentation := by
  introv R hs H
  algebraize [f]
  replace H : ∀ r ∈ s, Algebra.FinitePresentation R (Localization.Away (r : S)) := by
    intro r hr; simp_rw [RingHom.FinitePresentation] at H; convert H ⟨r, hr⟩; ext
    simp_rw [Algebra.smul_def]; rfl
  exact Algebra.FinitePresentation.of_span_eq_top_target s hs H

theorem finitePresentation_isLocal : PropertyIsLocal @FinitePresentation :=
  ⟨finitePresentation_localizationPreserves.away,
    finitePresentation_ofLocalizationSpanTarget,
    finitePresentation_ofLocalizationSpanTarget.ofLocalizationSpan
      (finitePresentation_stableUnderComposition.stableUnderCompositionWithLocalizationAway
        finitePresentation_holdsForLocalizationAway).left,
    (finitePresentation_stableUnderComposition.stableUnderCompositionWithLocalizationAway
      finitePresentation_holdsForLocalizationAway).right⟩

end RingHom
