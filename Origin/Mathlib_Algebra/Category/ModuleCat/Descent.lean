/-
Extracted from Algebra/Category/ModuleCat/Descent.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Faithfully flat descent for modules

In this file we show that extension of scalars by a faithfully flat ring homomorphism is comonadic.
Then the general theory of descent implies that the pseudofunctor to `Cat` given by extension
of scalars has effective descent relative to faithfully flat maps (TODO).

## Notes

This contribution was created as part of the AIM workshop
"Formalizing algebraic geometry" in June 2024.
-/

universe u

noncomputable section

open CategoryTheory Comonad ModuleCat Limits MonoidalCategory

variable {A B : Type u} [CommRing A] [CommRing B] {f : A →+* B}

lemma ModuleCat.preservesFiniteLimits_tensorLeft_of_ringHomFlat (hf : f.Flat) :
    PreservesFiniteLimits <| tensorLeft ((restrictScalars f).obj (ModuleCat.of B B)) := by
  algebraize [f]
  change PreservesFiniteLimits <| tensorLeft (ModuleCat.of A B)
  infer_instance

lemma ModuleCat.preservesFiniteLimits_extendScalars_of_flat (hf : f.Flat) :
    PreservesFiniteLimits (extendScalars.{_, _, u} f) := by
  have : PreservesFiniteLimits (extendScalars.{_, _, u} f ⋙ restrictScalars.{_, _, u} f) :=
    ModuleCat.preservesFiniteLimits_tensorLeft_of_ringHomFlat hf
  exact preservesFiniteLimits_of_reflects_of_preserves (extendScalars f) (restrictScalars f)
