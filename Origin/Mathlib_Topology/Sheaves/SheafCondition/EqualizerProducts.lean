/-
Extracted from Topology/Sheaves/SheafCondition/EqualizerProducts.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The sheaf condition in terms of an equalizer of products

Here we set up the machinery for the "usual" definition of the sheaf condition,
e.g. as in https://stacks.math.columbia.edu/tag/0072
in terms of an equalizer diagram where the two objects are
`∏ᶜ F.obj (U i)` and `∏ᶜ F.obj (U i) ⊓ (U j)`.

We show that this sheaf condition is equivalent to the "pairwise intersections" sheaf condition when
the presheaf is valued in a category with products, and thereby equivalent to the default sheaf
condition.
-/

universe v' v u

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopologicalSpace.Opens

namespace TopCat

variable {C : Type u} [Category.{v} C] [HasProducts.{v'} C]

variable {X : TopCat.{v'}} (F : Presheaf C X) {ι : Type v'} (U : ι → Opens X)

namespace Presheaf

namespace SheafConditionEqualizerProducts

def piOpens : C :=
  ∏ᶜ fun i : ι => F.obj (op (U i))

def piInters : C :=
  ∏ᶜ fun p : ι × ι => F.obj (op (U p.1 ⊓ U p.2))

def leftRes : piOpens F U ⟶ piInters.{v'} F U :=
  Pi.lift fun p : ι × ι => Pi.π _ p.1 ≫ F.map (infLELeft (U p.1) (U p.2)).op

def rightRes : piOpens F U ⟶ piInters.{v'} F U :=
  Pi.lift fun p : ι × ι => Pi.π _ p.2 ≫ F.map (infLERight (U p.1) (U p.2)).op

def res : F.obj (op (iSup U)) ⟶ piOpens.{v'} F U :=
  Pi.lift fun i : ι => F.map (TopologicalSpace.Opens.leSupr U i).op

set_option backward.isDefEq.respectTransparency false in
