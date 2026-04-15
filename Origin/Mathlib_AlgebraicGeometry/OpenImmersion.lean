/-
Extracted from AlgebraicGeometry/OpenImmersion.lean
Genuine: 4 of 5 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Open immersions of schemes

-/

noncomputable section

open TopologicalSpace CategoryTheory Opposite Topology

open CategoryTheory.Limits

namespace AlgebraicGeometry

universe v v₁ v₂ u

variable {C : Type u} [Category.{v} C]

abbrev IsOpenImmersion : MorphismProperty (Scheme.{u}) :=
  fun _ _ f ↦ LocallyRingedSpace.IsOpenImmersion f.toLRSHom

-- INSTANCE (free from Core): IsOpenImmersion.comp

namespace LocallyRingedSpace.IsOpenImmersion

protected def scheme (X : LocallyRingedSpace.{u})
    (h :
      ∀ x : X,
        ∃ (R : CommRingCat) (f : Spec.toLocallyRingedSpace.obj (op R) ⟶ X),
          (x ∈ Set.range f.base :) ∧ LocallyRingedSpace.IsOpenImmersion f) :
    Scheme where
  toLocallyRingedSpace := X
  local_affine := by
    intro x
    obtain ⟨R, f, h₁, h₂⟩ := h x
    refine ⟨⟨⟨_, h₂.base_open.isOpen_range⟩, h₁⟩, R, ⟨?_⟩⟩
    apply LocallyRingedSpace.isoOfSheafedSpaceIso
    refine SheafedSpace.forgetToPresheafedSpace.preimageIso ?_
    apply PresheafedSpace.IsOpenImmersion.isoOfRangeEq (PresheafedSpace.ofRestrict _ _) f.1
    exact Subtype.range_coe_subtype

end LocallyRingedSpace.IsOpenImmersion

theorem IsOpenImmersion.isOpen_range {X Y : Scheme.{u}} (f : X ⟶ Y) [H : IsOpenImmersion f] :
    IsOpen (Set.range f) :=
  H.base_open.isOpen_range

namespace Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [H : IsOpenImmersion f]

theorem isOpenEmbedding : IsOpenEmbedding f :=
  H.base_open
