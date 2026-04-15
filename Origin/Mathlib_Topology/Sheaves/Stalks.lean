/-
Extracted from Topology/Sheaves/Stalks.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Stalks

For a presheaf `F` on a topological space `X`, valued in some category `C`, the *stalk* of `F`
at the point `x : X` is defined as the colimit of the composition of the inclusion of categories
`(OpenNhds x)ᵒᵖ ⥤ (Opens X)ᵒᵖ` and the functor `F : (Opens X)ᵒᵖ ⥤ C`.
For an open neighborhood `U` of `x`, we define the map `F.germ x : F.obj (op U) ⟶ F.stalk x` as the
canonical morphism into this colimit.

Taking stalks is functorial: For every point `x : X` we define a functor `stalkFunctor C x`,
sending presheaves on `X` to objects of `C`. Furthermore, for a map `f : X ⟶ Y` between
topological spaces, we define `stalkPushforward` as the induced map on the stalks
`(f _* ℱ).stalk (f x) ⟶ ℱ.stalk x`.

Some lemmas about stalks and germs only hold for certain classes of concrete categories. A basic
property of forgetful functors of categories of algebraic structures (like `MonCat`,
`CommRingCat`,...) is that they preserve filtered colimits. Since stalks are filtered colimits,
this ensures that the stalks of presheaves valued in these categories behave exactly as for
`Type`-valued presheaves. For example, in `germ_exist` we prove that in such a category, every
element of the stalk is the germ of a section.

Furthermore, if we require the forgetful functor to reflect isomorphisms and preserve limits (as
is the case for most algebraic structures), we have access to the unique gluing API and can prove
further properties. Most notably, in `is_iso_iff_stalk_functor_map_iso`, we prove that in such
a category, a morphism of sheaves is an isomorphism if and only if all of its stalk maps are
isomorphisms.

See also the definition of "algebraic structures" in the stacks project:
https://stacks.math.columbia.edu/tag/007L

TODO(@joelriou): refactor the definitions in this file so as to make them
particular cases of general constructions for points of sites from
`Mathlib/CategoryTheory/Sites/Point/Basic.lean`.

-/

assert_not_exists IsOrderedMonoid

noncomputable section

universe v u v' u'

open CategoryTheory

open TopCat

open CategoryTheory.Limits CategoryTheory.Functor

open TopologicalSpace Topology

open Opposite

open scoped AlgebraicGeometry

variable {C : Type u} [Category.{v} C]

variable [HasColimits.{v} C]

variable {X Y Z : TopCat.{v}}

namespace TopCat.Presheaf

variable (C) in

def stalkFunctor (x : X) : X.Presheaf C ⥤ C :=
  (whiskeringLeft _ _ C).obj (OpenNhds.inclusion x).op ⋙ colim

def stalk (ℱ : X.Presheaf C) (x : X) : C :=
  (stalkFunctor C x).obj ℱ
