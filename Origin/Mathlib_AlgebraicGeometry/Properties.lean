/-
Extracted from AlgebraicGeometry/Properties.lean
Genuine: 6 of 13 | Dissolved: 0 | Infrastructure: 7
-/
import Origin.Core

/-!
# Basic properties of schemes

We provide some basic properties of schemes

## Main definition
* `AlgebraicGeometry.IsIntegral`: A scheme is integral if it is nontrivial and all nontrivial
  components of the structure sheaf are integral domains.
* `AlgebraicGeometry.IsReduced`: A scheme is reduced if all the components of the structure sheaf
  are reduced.
-/

universe u

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits TopCat Topology

namespace AlgebraicGeometry

variable (X : Scheme)

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): {X

-- INSTANCE (free from Core): :

class IsReduced : Prop where
  component_reduced : ∀ U, _root_.IsReduced Γ(X, U) := by infer_instance

attribute [instance] IsReduced.component_reduced

theorem isReduced_of_isReduced_stalk [∀ x : X, _root_.IsReduced (X.presheaf.stalk x)] :
    IsReduced X := by
  refine ⟨fun U => ⟨fun s hs => ?_⟩⟩
  apply Presheaf.section_ext X.sheaf U s 0
  intro x hx
  change (X.sheaf.presheaf.germ U x hx) s = (X.sheaf.presheaf.germ U x hx) 0
  rw [map_zero]
  change X.presheaf.germ U x hx s = 0
  exact (hs.map _).eq_zero

-- INSTANCE (free from Core): isReduced_stalk_of_isReduced

theorem isReduced_of_isOpenImmersion {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f]
    [IsReduced Y] : IsReduced X := by
  constructor
  intro U
  rw [← f.preimage_image_eq U]
  exact isReduced_of_injective (inv <| f.app (f ''ᵁ U)).hom
    (asIso <| f.app (f ''ᵁ U) : Γ(Y, f ''ᵁ U) ≅ _).symm.commRingCatIsoToRingEquiv.injective

-- INSTANCE (free from Core): {X

-- INSTANCE (free from Core): {R

theorem affine_isReduced_iff (R : CommRingCat) :
    IsReduced (Spec R) ↔ _root_.IsReduced R := by
  refine ⟨?_, fun h => inferInstance⟩
  intro h
  exact isReduced_of_injective (Scheme.ΓSpecIso R).inv.hom
    (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv.injective

theorem isReduced_of_isAffine_isReduced [IsAffine X] [_root_.IsReduced Γ(X, ⊤)] :
    IsReduced X :=
  isReduced_of_isOpenImmersion X.isoSpec.hom

theorem IsReduced.of_openCover (𝒰 : X.OpenCover) [∀ i, IsReduced (𝒰.X i)] : IsReduced X := by
  have (x : X) : _root_.IsReduced (X.presheaf.stalk x) := by
    obtain ⟨i, x, rfl⟩ := 𝒰.exists_eq x
    exact isReduced_of_injective _
      (asIso <| (𝒰.f i).stalkMap x).commRingCatIsoToRingEquiv.injective
  exact isReduced_of_isReduced_stalk _
