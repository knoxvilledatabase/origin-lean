/-
Extracted from CategoryTheory/Sites/Subsheaf.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Subsheaf of types

We define the subsheaf of a type-valued presheaf.

## Main results

- `CategoryTheory.Subfunctor.sheafify` :
  The sheafification of a subpresheaf as a subpresheaf. Note that this is a sheaf only when the
  whole sheaf is.
- `CategoryTheory.Subfunctor.sheafify_isSheaf` :
  The sheafification is a sheaf
- `CategoryTheory.Subfunctor.sheafifyLift` :
  The descent of a map into a sheaf to the sheafification.
- `CategoryTheory.GrothendieckTopology.imageSheaf` : The image sheaf of a morphism.
- `CategoryTheory.GrothendieckTopology.imageFactorization` : The image sheaf as a
  `Limits.imageFactorization`.
-/

universe w v u

open Opposite CategoryTheory

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

variable {F F' F'' : Cᵒᵖ ⥤ Type w} (G G' : Subfunctor F)

theorem Subfunctor.isSeparated {J : GrothendieckTopology C} (h : Presieve.IsSeparated J F) :
    Presieve.IsSeparated J G.toFunctor :=
  fun _ S hS _ _ _ hx₁ hx₂ ↦ Subtype.ext <| h S hS _ _ _ (hx₁.map G.ι) (hx₂.map G.ι)
