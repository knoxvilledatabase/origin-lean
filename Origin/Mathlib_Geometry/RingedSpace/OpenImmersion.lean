/-
Extracted from Geometry/RingedSpace/OpenImmersion.lean
Genuine: 4 of 6 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Open immersions of structured spaces

We say that a morphism of presheafed spaces `f : X ⟶ Y` is an open immersion if
the underlying map of spaces is an open embedding `f : X ⟶ U ⊆ Y`,
and the sheaf map `Y(V) ⟶ f _* X(V)` is an iso for each `V ⊆ U`.

Abbreviations are also provided for `SheafedSpace`, `LocallyRingedSpace` and `Scheme`.

## Main definitions

* `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion`: the `Prop`-valued typeclass asserting
  that a PresheafedSpace hom `f` is an open_immersion.
* `AlgebraicGeometry.IsOpenImmersion`: the `Prop`-valued typeclass asserting
  that a Scheme morphism `f` is an open_immersion.
* `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.isoRestrict`: The source of an
  open immersion is isomorphic to the restriction of the target onto the image.
* `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.lift`: Any morphism whose range is
  contained in an open immersion factors through the open immersion.
* `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toSheafedSpace`: If `f : X ⟶ Y` is an
  open immersion of presheafed spaces, and `Y` is a sheafed space, then `X` is also a sheafed
  space. The morphism as morphisms of sheafed spaces is given by `toSheafedSpaceHom`.
* `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toLocallyRingedSpace`: If `f : X ⟶ Y` is
  an open immersion of presheafed spaces, and `Y` is a locally ringed space, then `X` is also a
  locally ringed space. The morphism as morphisms of locally ringed spaces is given by
  `toLocallyRingedSpaceHom`.

## Main results

* `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.comp`: The composition of two open
  immersions is an open immersion.
* `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.ofIso`: An iso is an open immersion.
* `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.to_iso`:
  A surjective open immersion is an isomorphism.
* `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.stalk_iso`: An open immersion induces
  an isomorphism on stalks.
* `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.hasPullback_of_left`: If `f` is an open
  immersion, then the pullback `(f, g)` exists (and the forgetful functor to `TopCat` preserves it).
* `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullbackSndOfLeft`: Open immersions
  are stable under pullbacks.
* `AlgebraicGeometry.SheafedSpace.IsOpenImmersion.of_stalk_iso`: A (topological) open embedding
  between two sheafed spaces is an open immersion if all the stalk maps are isomorphisms.

-/

open TopologicalSpace CategoryTheory Opposite Topology

open CategoryTheory.Limits

namespace AlgebraicGeometry

universe w v v₁ v₂ u

variable {C : Type u} [Category.{v} C]

class PresheafedSpace.IsOpenImmersion {X Y : PresheafedSpace C} (f : X ⟶ Y) : Prop where
  /-- the underlying continuous map of underlying spaces from the source to an open subset of the
  target. -/
  base_open : IsOpenEmbedding f.base
  /-- the underlying sheaf morphism is an isomorphism on each open subset -/
  c_iso : ∀ U : Opens X, IsIso (f.c.app (op (base_open.functor.obj U)))

abbrev SheafedSpace.IsOpenImmersion {X Y : SheafedSpace C} (f : X ⟶ Y) : Prop :=
  PresheafedSpace.IsOpenImmersion f.hom

abbrev LocallyRingedSpace.IsOpenImmersion {X Y : LocallyRingedSpace} (f : X ⟶ Y) : Prop :=
  SheafedSpace.IsOpenImmersion f.toShHom

-- INSTANCE (free from Core): {X

namespace PresheafedSpace.IsOpenImmersion

open PresheafedSpace

local notation "IsOpenImmersion" => PresheafedSpace.IsOpenImmersion

attribute [instance] IsOpenImmersion.c_iso

variable {X Y : PresheafedSpace C} (f : X ⟶ Y) [H : IsOpenImmersion f]

abbrev opensFunctor :=
  H.base_open.functor

set_option backward.isDefEq.respectTransparency false in
