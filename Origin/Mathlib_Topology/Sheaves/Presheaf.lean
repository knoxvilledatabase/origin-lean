/-
Extracted from Topology/Sheaves/Presheaf.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Presheaves on a topological space

We define `TopCat.Presheaf C X` simply as `(TopologicalSpace.Opens X)ᵒᵖ ⥤ C`,
and inherit the category structure with natural transformations as morphisms.

We define
* Given `{X Y : TopCat.{w}}` and `f : X ⟶ Y`, we define
  `TopCat.Presheaf.pushforward C f : X.Presheaf C ⥤ Y.Presheaf C`,
  with notation `f _* ℱ` for `ℱ : X.Presheaf C`.

and for `ℱ : X.Presheaf C` provide the natural isomorphisms
* `TopCat.Presheaf.Pushforward.id : (𝟙 X) _* ℱ ≅ ℱ`
* `TopCat.Presheaf.Pushforward.comp : (f ≫ g) _* ℱ ≅ g _* (f _* ℱ)`
  along with their `@[simp]` lemmas.

We also define the functors `pullback C f : Y.Presheaf C ⥤ X.Presheaf c`,
and provide their adjunction at
`TopCat.Presheaf.pullbackPushforwardAdjunction`.
-/

universe w v u

open CategoryTheory TopologicalSpace Opposite Functor

variable (C : Type u) [Category.{v} C]

namespace TopCat

def Presheaf (X : TopCat.{w}) : Type max u v w :=
  (Opens X)ᵒᵖ ⥤ C

-- INSTANCE (free from Core): (X

variable {C}

namespace Presheaf
