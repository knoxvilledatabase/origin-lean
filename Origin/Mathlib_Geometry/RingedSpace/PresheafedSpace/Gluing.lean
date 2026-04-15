/-
Extracted from Geometry/RingedSpace/PresheafedSpace/Gluing.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Gluing structured spaces

Given a family of gluing data of structured spaces (presheafed spaces, sheafed spaces, or locally
ringed spaces), we may glue them together.

The construction should be "sealed" and considered as a black box, while only using the API
provided.

## Main definitions

* `AlgebraicGeometry.PresheafedSpace.GlueData`: A structure containing the family of gluing data.
* `CategoryTheory.GlueData.glued`: The glued presheafed space.
  This is defined as the multicoequalizer of `∐ V i j ⇉ ∐ U i`, so that the general colimit API
  can be used.
* `CategoryTheory.GlueData.ι`: The immersion `ι i : U i ⟶ glued` for each `i : J`.

## Main results

* `AlgebraicGeometry.PresheafedSpace.GlueData.ιIsOpenImmersion`: The map `ι i : U i ⟶ glued`
  is an open immersion for each `i : J`.
* `AlgebraicGeometry.PresheafedSpace.GlueData.ι_jointly_surjective` : The underlying maps of
  `ι i : U i ⟶ glued` are jointly surjective.
* `AlgebraicGeometry.PresheafedSpace.GlueData.vPullbackConeIsLimit` : `V i j` is the pullback
  (intersection) of `U i` and `U j` over the glued space.

Analogous results are also provided for `SheafedSpace` and `LocallyRingedSpace`.

## Implementation details

Almost the whole file is dedicated to showing that `ι i` is an open immersion. The fact that
this is an open embedding of topological spaces follows from `Mathlib/Topology/Gluing.lean`, and it
remains to construct `Γ(𝒪_{U_i}, U) ⟶ Γ(𝒪_X, ι i '' U)` for each `U ⊆ U i`.
Since `Γ(𝒪_X, ι i '' U)` is the limit of `diagram_over_open`, the components of the structure
sheaves of the spaces in the gluing diagram, we need to construct a map
`ιInvApp_π_app : Γ(𝒪_{U_i}, U) ⟶ Γ(𝒪_V, U_V)` for each `V` in the gluing diagram.

We will refer to ![this diagram](https://i.imgur.com/P0phrwr.png) in the following docstrings.
The `X` is the glued space, and the dotted arrow is a partial inverse guaranteed by the fact
that it is an open immersion. The map `Γ(𝒪_{U_i}, U) ⟶ Γ(𝒪_{U_j}, _)` is given by the composition
of the red arrows, and the map `Γ(𝒪_{U_i}, U) ⟶ Γ(𝒪_{V_{jk}}, _)` is given by the composition of the
blue arrows. To lift this into a map from `Γ(𝒪_X, ι i '' U)`, we also need to show that these
commute with the maps in the diagram (the green arrows), which is just a lengthy diagram-chasing.

-/

noncomputable section

open TopologicalSpace CategoryTheory Opposite Topology

open CategoryTheory.Limits AlgebraicGeometry.PresheafedSpace

open AlgebraicGeometry.PresheafedSpace.IsOpenImmersion

open CategoryTheory.GlueData

namespace AlgebraicGeometry

universe v u

variable (C : Type u) [Category.{v} C]

namespace PresheafedSpace

structure GlueData extends CategoryTheory.GlueData (PresheafedSpace.{v, u, v} C) where
  f_open : ∀ i j, IsOpenImmersion (f i j)

attribute [instance] GlueData.f_open

namespace GlueData

variable {C}

variable (D : GlueData.{v, u} C)

local notation "𝖣" => D.toGlueData

local notation "π₁ " i ", " j ", " k => pullback.fst (D.f i j) (D.f i k)

local notation "π₂ " i ", " j ", " k => pullback.snd (D.f i j) (D.f i k)

set_option quotPrecheck false

local notation "π₁⁻¹ " i ", " j ", " k =>

  (PresheafedSpace.IsOpenImmersion.pullbackFstOfRight (D.f i j) (D.f i k)).invApp

set_option quotPrecheck false

local notation "π₂⁻¹ " i ", " j ", " k =>

  (PresheafedSpace.IsOpenImmersion.pullbackSndOfLeft (D.f i j) (D.f i k)).invApp

abbrev toTopGlueData : TopCat.GlueData :=
  { f_open := fun i j => (D.f_open i j).base_open
    toGlueData := 𝖣.mapGlueData (forget C) }

set_option backward.isDefEq.respectTransparency false in

theorem ι_isOpenEmbedding [HasLimits C] (i : D.J) : IsOpenEmbedding (𝖣.ι i).base := by
  rw [← show _ = (𝖣.ι i).base from 𝖣.ι_gluedIso_inv (PresheafedSpace.forget _) _, TopCat.coe_comp]
  exact (TopCat.homeoOfIso (𝖣.gluedIso (PresheafedSpace.forget _)).symm).isOpenEmbedding.comp
      (D.toTopGlueData.ι_isOpenEmbedding i)

set_option backward.isDefEq.respectTransparency false in

theorem pullback_base (i j k : D.J) (S : Set (D.V (i, j)).carrier) :
    (π₂ i, j, k) '' ((π₁ i, j, k) ⁻¹' S) = D.f i k ⁻¹' (D.f i j '' S) := by
  have eq₁ : _ = (π₁ i, j, k).base := PreservesPullback.iso_hom_fst (forget C) _ _
  have eq₂ : _ = (π₂ i, j, k).base := PreservesPullback.iso_hom_snd (forget C) _ _
  rw [← eq₁, ← eq₂, TopCat.coe_comp, Set.image_comp, TopCat.coe_comp, Set.preimage_comp,
    Set.image_preimage_eq]
  · simp only [forget_obj, forget_map, TopCat.pullback_snd_image_fst_preimage]
  rw [← TopCat.epi_iff_surjective]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
