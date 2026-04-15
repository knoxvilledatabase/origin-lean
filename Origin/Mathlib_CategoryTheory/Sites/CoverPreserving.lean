/-
Extracted from CategoryTheory/Sites/CoverPreserving.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Cover-preserving functors between sites.

In order to show that a functor is continuous, we define cover-preserving functors
between sites as functors that push covering sieves to covering sieves.
Then, a cover-preserving and compatible-preserving functor is continuous.

## Main definitions

* `CategoryTheory.CoverPreserving`: a functor between sites is cover-preserving if it
  pushes covering sieves to covering sieves
* `CategoryTheory.CompatiblePreserving`: a functor between sites is compatible-preserving
  if it pushes compatible families of elements to compatible families.

## Main results

- `CategoryTheory.isContinuous_of_coverPreserving`: If `G : C ⥤ D` is
  cover-preserving and compatible-preserving, then `G` is a continuous functor,
  i.e. `G.op ⋙ -` as a functor `(Dᵒᵖ ⥤ A) ⥤ (Cᵒᵖ ⥤ A)` of presheaves maps sheaves to sheaves.

## References

* [Elephant]: *Sketches of an Elephant*, P. T. Johnstone: C2.3.
* https://stacks.math.columbia.edu/tag/00WU

-/

universe w v₁ v₂ v₃ u₁ u₂ u₃

noncomputable section

open CategoryTheory Opposite CategoryTheory.Presieve.FamilyOfElements CategoryTheory.Presieve

  CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)

variable {A : Type u₃} [Category.{v₃} A]

variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)

variable {L : GrothendieckTopology A}

structure CoverPreserving (G : C ⥤ D) : Prop where
  cover_preserve : ∀ {U : C} {S : Sieve U} (_ : S ∈ J U), S.functorPushforward G ∈ K (G.obj U)

theorem idCoverPreserving : CoverPreserving J J (𝟭 _) :=
  ⟨fun hS => by simpa using hS⟩

theorem CoverPreserving.comp {F} (hF : CoverPreserving J K F) {G} (hG : CoverPreserving K L G) :
    CoverPreserving J L (F ⋙ G) :=
  ⟨fun hS => by
    rw [Sieve.functorPushforward_comp]
    exact hG.cover_preserve (hF.cover_preserve hS)⟩

structure CompatiblePreserving (K : GrothendieckTopology D) (G : C ⥤ D) : Prop where
  compatible :
    ∀ (ℱ : Sheaf K (Type w)) {Z} {T : Presieve Z} {x : FamilyOfElements (G.op ⋙ ℱ.obj) T}
      (_ : x.Compatible) {Y₁ Y₂} {X} (f₁ : X ⟶ G.obj Y₁) (f₂ : X ⟶ G.obj Y₂) {g₁ : Y₁ ⟶ Z}
      {g₂ : Y₂ ⟶ Z} (hg₁ : T g₁) (hg₂ : T g₂) (_ : f₁ ≫ G.map g₁ = f₂ ≫ G.map g₂),
      ℱ.obj.map f₁.op (x g₁ hg₁) = ℱ.obj.map f₂.op (x g₂ hg₂)

variable {J K} {G : C ⥤ D} (hG : CompatiblePreserving.{w} K G) (ℱ : Sheaf K (Type w)) {Z : C}

variable {T : Presieve Z} {x : FamilyOfElements (G.op ⋙ ℱ.obj) T} (h : x.Compatible)

include hG h

theorem Presieve.FamilyOfElements.Compatible.functorPushforward :
    (x.functorPushforward G).Compatible := by
  rintro Z₁ Z₂ W g₁ g₂ f₁' f₂' H₁ H₂ eq
  unfold FamilyOfElements.functorPushforward
  rcases getFunctorPushforwardStructure H₁ with ⟨X₁, f₁, h₁, hf₁, rfl⟩
  rcases getFunctorPushforwardStructure H₂ with ⟨X₂, f₂, h₂, hf₂, rfl⟩
  suffices ℱ.obj.map (g₁ ≫ h₁).op (x f₁ hf₁) = ℱ.obj.map (g₂ ≫ h₂).op (x f₂ hf₂) by
    simpa using this
  apply hG.compatible ℱ h _ _ hf₁ hf₂
  simpa using eq
