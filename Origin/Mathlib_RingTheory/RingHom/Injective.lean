/-
Extracted from RingTheory/RingHom/Injective.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.RingTheory.RingHomProperties

/-! # Meta properties of injective ring homomorphisms -/

lemma _root_.RingHom.injective_stableUnderComposition :
    RingHom.StableUnderComposition (fun f ↦ Function.Injective f) := by
  intro R S T _ _ _ f g hf hg
  simp only [RingHom.coe_comp]
  exact Function.Injective.comp hg hf

lemma _root_.RingHom.injective_respectsIso :
    RingHom.RespectsIso (fun f ↦ Function.Injective f) := by
  apply RingHom.injective_stableUnderComposition.respectsIso
  intro R S _ _ e
  exact e.bijective.injective
