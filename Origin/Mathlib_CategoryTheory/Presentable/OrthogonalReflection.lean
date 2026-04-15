/-
Extracted from CategoryTheory/Presentable/OrthogonalReflection.lean
Genuine: 8 of 9 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# The Orthogonal-reflection construction

Given `W : MorphismProperty C` (which should be small) and assuming the existence
of certain colimits in `C`, we construct a morphism `toSucc W Z : Z ⟶ succ W Z` for
any `Z : C`. This morphism belongs to `W.isLocal.isLocal` and
is an isomorphism iff `Z` belongs to `W.isLocal` (see the lemma `isIso_toSucc_iff`).
The morphism `toSucc W Z : Z ⟶ succ W Z` is defined as a composition
of two morphisms that are roughly described as follows:
* `toStep W Z : Z ⟶ step W Z`: for any morphism `f : X ⟶ Y` satisfying `W`
  and any morphism `X ⟶ Z`, we "attach" a morphism `Y ⟶ step W Z` (using
  coproducts and a pushout in essentially the same way as it is done in
  the file `Mathlib/CategoryTheory/SmallObject/Construction.lean` for the small object
  argument);
* `fromStep W Z : step W Z ⟶ succ W Z`: this morphism coequalizes all pairs
  of morphisms `g₁ g₂ : Y ⟶ step W Z` such that there is a `f : X ⟶ Y`
  satisfying `W` such that `f ≫ g₁ = f ≫ g₂`.

The morphism `toSucc W Z : Z ⟶ succ W Z` is a variant of the (wrong) definition
p. 32 in the book by Adámek and Rosický. In this book, a slightly different object
than `succ W Z` is defined directly as a colimit of an intricate diagram, but
contrary to what is stated on p. 33, it does not satisfy `isIso_toSucc_iff`.
The author of this file was unable to understand the attempt of the authors
to fix this mistake in the errata to this book. This led to the definition
in two steps outlined above.

## Main results

The morphisms described above `toSucc W Z : Z ⟶ succ W Z` for all `Z : C` allow to
define `succStruct W Z₀ : SuccStruct C` for any `Z₀ : C`. By applying
a transfinite iteration to this `SuccStruct`, we obtain the following results
under the assumption that `W : MorphismProperty C` is a `w`-small property
of morphisms in a locally `κ`-presentable category `C` (with `κ : Cardinal.{w}`
a regular cardinal) such that the domains and codomains of the morphisms
satisfying `W` are `κ`-presentable:
* `MorphismProperty.isRightAdjoint_ι_isLocal`: existence of the left adjoint
  of the inclusion `W.isLocal ⥤ C`;
* `MorphismProperty.isLocallyPresentable_isLocal`: the full subcategory
  `W.isLocal` is locally presentable.

This is essentially the implication (i) → (ii) in Theorem 1.39 (and the corollary 1.40)
in the book by Adámek and Rosický (note that according to the
errata to this book, the implication (ii) → (i) is wrong when `κ = ℵ₀`).

## References
* [Adámek, J. and Rosický, J., *Locally presentable and accessible categories*][Adamek_Rosicky_1994]

-/

universe w v' u' v u

namespace CategoryTheory

open Limits Localization Opposite

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)

set_option backward.isDefEq.respectTransparency false in

lemma MorphismProperty.isClosedUnderColimitsOfShape_isLocal
    (J : Type u') [Category.{v'} J] [EssentiallySmall.{w} J]
    (κ : Cardinal.{w}) [Fact κ.IsRegular] [IsCardinalFiltered J κ]
    (hW : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), W f → IsCardinalPresentable X κ ∧ IsCardinalPresentable Y κ) :
    W.isLocal.IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := fun Z ⟨p⟩ X Y f hf ↦ by
    obtain ⟨_, _⟩ := hW f hf
    refine ⟨fun g₁ g₂ h ↦ ?_, fun g ↦ ?_⟩
    · obtain ⟨j₁, g₁, rfl⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ p.isColimit g₁
      obtain ⟨j₂, g₂, rfl⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ p.isColimit g₂
      dsimp at h ⊢
      obtain ⟨j₃, u, v, huv⟩ :=
        IsCardinalPresentable.exists_eq_of_isColimit κ p.isColimit (f ≫ g₁) (f ≫ g₂)
          (by simpa)
      simp only [Category.assoc] at huv
      rw [← p.w u, ← p.w v, reassoc_of% ((p.prop_diag_obj j₃ _ hf).1 huv)]
    · obtain ⟨j, g, rfl⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ p.isColimit g
      obtain ⟨g, rfl⟩ := (p.prop_diag_obj j _ hf).2 g
      exact ⟨g ≫ p.ι.app j, by simp⟩

lemma MorphismProperty.isCardinalAccessible_ι_isLocal
    (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [HasCardinalFilteredColimits C κ]
    (hW : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), W f → IsCardinalPresentable X κ ∧ IsCardinalPresentable Y κ) :
    W.isLocal.ι.IsCardinalAccessible κ where
  preservesColimitOfShape J _ _ := by
    have := W.isClosedUnderColimitsOfShape_isLocal J κ hW
    infer_instance

namespace OrthogonalReflection

variable (Z : C)

def D₁ : Type _ := Σ (f : W.toSet), f.1.left ⟶ Z

-- INSTANCE (free from Core): [MorphismProperty.IsSmall.{w}

lemma D₁.hasCoproductsOfShape [MorphismProperty.IsSmall.{w} W]
    [LocallySmall.{w} C] [HasCoproducts.{w} C] :
    HasCoproductsOfShape (D₁ (W := W) (Z := Z)) C :=
  hasColimitsOfShape_of_equivalence
    (Discrete.equivalence (equivShrink.{w} _).symm)

variable {W Z} in

def D₁.obj₁ (d : D₁ W Z) : C := d.1.1.left

variable {W Z} in

def D₁.obj₂ (d : D₁ W Z) : C := d.1.1.right

variable [HasCoproduct (D₁.obj₁ (W := W) (Z := Z))]

noncomputable abbrev D₁.l : ∐ (obj₁ (W := W) (Z := Z)) ⟶ Z :=
  Sigma.desc (fun d ↦ d.2)

variable {W Z} in

noncomputable abbrev D₁.ιLeft {X Y : C} (f : X ⟶ Y) (hf : W f) (g : X ⟶ Z) :
    X ⟶ ∐ obj₁ (W := W) (Z := Z) :=
  Sigma.ι (obj₁ (W := W) (Z := Z)) ⟨⟨Arrow.mk f, hf⟩, g⟩

variable {W Z} in
