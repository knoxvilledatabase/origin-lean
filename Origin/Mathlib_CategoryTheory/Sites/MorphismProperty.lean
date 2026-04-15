/-
Extracted from CategoryTheory/Sites/MorphismProperty.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The site induced by a morphism property

Let `C` be a category with pullbacks and `P` be a multiplicative morphism property which is
stable under base change. Then `P` induces a pretopology, where coverings are given by presieves
whose elements satisfy `P`.

Standard examples of pretopologies in algebraic geometry, such as the étale site, are obtained from
this construction by intersecting with the pretopology of surjective families.

-/

universe w

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C]

namespace MorphismProperty

variable {P Q : MorphismProperty C}

def precoverage (P : MorphismProperty C) : Precoverage C where
  coverings X := {S | ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f → P f}
