/-
Extracted from AlgebraicGeometry/Cover/Open.lean
Genuine: 4 of 7 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Open covers of schemes

This file provides the basic API for open covers of schemes.

## Main definition
- `AlgebraicGeometry.Scheme.OpenCover`: The type of open covers of a scheme `X`,
  consisting of a family of open immersions into `X`,
  and for each `x : X` an open immersion (indexed by `f x`) that covers `x`.
- `AlgebraicGeometry.Scheme.affineCover`: `X.affineCover` is a choice of an affine cover of `X`.
- `AlgebraicGeometry.Scheme.AffineOpenCover`: The type of affine open covers of a scheme `X`.
-/

noncomputable section

open TopologicalSpace CategoryTheory Opposite CategoryTheory.Limits

universe v v₁ v₂ u

namespace AlgebraicGeometry

namespace Scheme

-- INSTANCE (free from Core): :

abbrev OpenCover (X : Scheme.{u}) : Type _ := Cover.{v} (precoverage @IsOpenImmersion) X

variable {X Y Z : Scheme.{u}} (𝒰 : OpenCover X) (f : X ⟶ Z) (g : Y ⟶ Z)

variable [∀ x, HasPullback (𝒰.f x ≫ f) g]

-- INSTANCE (free from Core): (i

set_option backward.isDefEq.respectTransparency false in

def affineCover (X : Scheme.{u}) : OpenCover X := by
  choose U R h using X.local_affine
  let e (x) := (h x).some
  exact
  { I₀ := X
    X x := Spec (R x)
    f x := ⟨(e x).inv ≫ X.toLocallyRingedSpace.ofRestrict _⟩
    mem₀ := by
      rw [presieve₀_mem_precoverage_iff]
      refine ⟨fun x ↦ ⟨x, ⟨(e x).hom.base ⟨x, (U x).2⟩, ?_⟩⟩, inferInstance⟩
      change ((((e x).hom ≫ (e x).inv).base ≫ (X.ofRestrict _).base)) ⟨x, _⟩ = x
      cat_disch }

-- INSTANCE (free from Core): :

theorem OpenCover.iSup_opensRange {X : Scheme.{u}} (𝒰 : X.OpenCover) :
    ⨆ i, (𝒰.f i).opensRange = ⊤ :=
  Opens.ext <| by rw [Opens.coe_iSup]; exact 𝒰.iUnion_range

lemma OpenCover.isOpenCover_opensRange {X : Scheme.{u}} (𝒰 : X.OpenCover) :
    IsOpenCover fun i ↦ (𝒰.f i).opensRange :=
  .mk 𝒰.iSup_opensRange
