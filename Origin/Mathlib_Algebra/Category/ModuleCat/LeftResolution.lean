/-
Extracted from Algebra/Category/ModuleCat/LeftResolution.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Functorial projective resolutions of modules

The fact that an `R`-module `M` can be functorially written as a quotient of a
projective `R`-module is expressed as the definition `ModuleCat.projectiveResolution`.
Using the construction in the file `Mathlib/Algebra/Homology/LeftResolution/Basic.lean`,
we may obtain a functor `(projectiveResolution R).chainComplexFunctor` which
sends `M : ModuleCat R` to a projective resolution.

-/

universe u

variable (R : Type u) [Ring R]

namespace ModuleCat

open CategoryTheory Abelian

-- INSTANCE (free from Core): (X

set_option backward.isDefEq.respectTransparency false in

noncomputable def projectiveResolution :
    LeftResolution (ObjectProperty.ι (isProjective (ModuleCat.{u} R))) where
  F := ObjectProperty.lift _ (forget _ ⋙ free R) (by dsimp; infer_instance)
  π := (adj R).counit

end ModuleCat
