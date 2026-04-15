/-
Extracted from CategoryTheory/Preadditive/Projective/Internal.lean
Genuine: 3 of 5 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!

# Internal projectivity

This file defines internal projectivity of objects `P` in a category `C` as a class
`InternallyProjective P`. This means that the functor taking internal homs out of `P`
preserves epimorphisms. It also proves that a retract of an internally projective object
is internally projective (see `InternallyProjective.ofRetract`).

This property is important in the setting of light condensed abelian groups, when establishing
the solid theory (see the lecture series on analytic stacks:
https://www.youtube.com/playlist?list=PLx5f8IelFRgGmu6gmL-Kf_Rl_6Mm7juZO).
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed Limits Functor

namespace CategoryTheory

variable {C : Type*} [Category* C] [MonoidalCategory C] [MonoidalClosed C]

def isInternallyProjective : ObjectProperty C := fun P ↦ (ihom P).PreservesEpimorphisms

abbrev InternallyProjective (P : C) := isInternallyProjective.Is P

-- INSTANCE (free from Core): InternallyProjective.preserves_epi

-- INSTANCE (free from Core): :

namespace InternallyProjective

lemma ofRetract {X Y : C} (r : Retract Y X) [InternallyProjective X] : InternallyProjective Y :=
  ⟨isInternallyProjective.prop_of_retract r (isInternallyProjective.prop_of_is _)⟩

end CategoryTheory.InternallyProjective
