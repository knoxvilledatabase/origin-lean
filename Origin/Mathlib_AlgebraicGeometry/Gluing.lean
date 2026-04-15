/-
Extracted from AlgebraicGeometry/Gluing.lean
Genuine: 8 of 17 | Dissolved: 0 | Infrastructure: 9
-/
import Origin.Core

/-!
# Gluing Schemes

Given a family of gluing data of schemes, we may glue them together.
Also see the section about "locally directed" gluing,
which is a special case where the conditions are easier to check.

## Main definitions

* `AlgebraicGeometry.Scheme.GlueData`: A structure containing the family of gluing data.
* `AlgebraicGeometry.Scheme.GlueData.glued`: The glued scheme.
    This is defined as the multicoequalizer of `∐ V i j ⇉ ∐ U i`, so that the general colimit API
    can be used.
* `AlgebraicGeometry.Scheme.GlueData.ι`: The immersion `ι i : U i ⟶ glued` for each `i : J`.
* `AlgebraicGeometry.Scheme.GlueData.isoCarrier`: The isomorphism between the underlying space
  of the glued scheme and the gluing of the underlying topological spaces.
* `AlgebraicGeometry.Scheme.OpenCover.gluedCover`: The glue data associated with an open cover.
* `AlgebraicGeometry.Scheme.OpenCover.fromGlued`: The canonical morphism
  `𝒰.gluedCover.glued ⟶ X`. This has an `is_iso` instance.
* `AlgebraicGeometry.Scheme.OpenCover.glueMorphisms`: We may glue a family of compatible
  morphisms defined on an open cover of a scheme.

## Main results

* `AlgebraicGeometry.Scheme.GlueData.ι_isOpenImmersion`: The map `ι i : U i ⟶ glued`
  is an open immersion for each `i : J`.
* `AlgebraicGeometry.Scheme.GlueData.ι_jointly_surjective` : The underlying maps of
  `ι i : U i ⟶ glued` are jointly surjective.
* `AlgebraicGeometry.Scheme.GlueData.vPullbackConeIsLimit` : `V i j` is the pullback
  (intersection) of `U i` and `U j` over the glued space.
* `AlgebraicGeometry.Scheme.GlueData.ι_eq_iff` : `ι i x = ι j y` if and only if they coincide
  when restricted to `V i i`.
* `AlgebraicGeometry.Scheme.GlueData.isOpen_iff` : A subset of the glued scheme is open iff
  all its preimages in `U i` are open.

## Implementation details

All the hard work is done in `Mathlib/Geometry/RingedSpace/PresheafedSpace/Gluing.lean` where we
glue presheafed spaces, sheafed spaces, and locally ringed spaces.

-/

noncomputable section

universe v u

open TopologicalSpace CategoryTheory Opposite Topology

open CategoryTheory.Limits AlgebraicGeometry.PresheafedSpace

open CategoryTheory.GlueData

namespace AlgebraicGeometry

namespace Scheme

structure GlueData extends CategoryTheory.GlueData Scheme where
  f_open : ∀ i j, IsOpenImmersion (f i j)

attribute [instance] GlueData.f_open

namespace GlueData

variable (D : GlueData.{u})

local notation "𝖣" => D.toGlueData

abbrev toLocallyRingedSpaceGlueData : LocallyRingedSpace.GlueData :=
  { f_open := D.f_open
    toGlueData := 𝖣.mapGlueData forgetToLocallyRingedSpace }

-- INSTANCE (free from Core): (i

-- INSTANCE (free from Core): (i

-- INSTANCE (free from Core): (i

-- INSTANCE (free from Core): (i

set_option backward.isDefEq.respectTransparency false in

def gluedScheme : Scheme := by
  apply LocallyRingedSpace.IsOpenImmersion.scheme
    D.toLocallyRingedSpaceGlueData.toGlueData.glued
  intro x
  obtain ⟨i, y, rfl⟩ := D.toLocallyRingedSpaceGlueData.ι_jointly_surjective x
  obtain ⟨j, z, hz⟩ := (D.U i).affineCover.exists_eq y
  refine ⟨_, ((D.U i).affineCover.f j).toLRSHom ≫
    D.toLocallyRingedSpaceGlueData.toGlueData.ι i, ?_⟩
  constructor
  · simp only [LocallyRingedSpace.comp_toHom, PresheafedSpace.comp_base,
      TopCat.hom_comp, ContinuousMap.coe_comp, Set.range_comp]
    exact Set.mem_image_of_mem _ ⟨z, hz⟩
  · infer_instance

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

abbrev glued : Scheme :=
  𝖣.glued

abbrev ι (i : D.J) : D.U i ⟶ D.glued :=
  𝖣.ι i

abbrev isoLocallyRingedSpace :
    D.glued.toLocallyRingedSpace ≅ D.toLocallyRingedSpaceGlueData.toGlueData.glued :=
  𝖣.gluedIso forgetToLocallyRingedSpace

theorem ι_isoLocallyRingedSpace_inv (i : D.J) :
    D.toLocallyRingedSpaceGlueData.toGlueData.ι i ≫
      D.isoLocallyRingedSpace.inv = (𝖣.ι i).toLRSHom :=
  𝖣.ι_gluedIso_inv forgetToLocallyRingedSpace i

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): ι_isOpenImmersion

theorem ι_jointly_surjective (x : 𝖣.glued.carrier) :
    ∃ (i : D.J) (y : (D.U i).carrier), D.ι i y = x :=
  𝖣.ι_jointly_surjective forget x
