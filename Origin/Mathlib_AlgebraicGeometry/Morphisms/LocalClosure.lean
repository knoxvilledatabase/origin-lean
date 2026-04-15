/-
Extracted from AlgebraicGeometry/Morphisms/LocalClosure.lean
Genuine: 5 of 13 | Dissolved: 0 | Infrastructure: 8
-/
import Origin.Core

/-!
# Local closure of morphism properties

We define the source local closure of a property `P` w.r.t. a morphism property `W` and show it
inherits stability properties from `P`.
-/

universe u

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry

variable (W : MorphismProperty Scheme.{u})

def sourceLocalClosure (P : MorphismProperty Scheme.{u}) : MorphismProperty Scheme.{u} :=
  fun X _ f ↦ ∃ (𝒰 : Scheme.Cover.{u} (Scheme.precoverage W) X), ∀ (i : 𝒰.I₀), P (𝒰.f i ≫ f)

namespace sourceLocalClosure

variable {W} {P Q : MorphismProperty Scheme.{u}} {X Y : Scheme.{u}}

noncomputable def cover {f : X ⟶ Y} (hf : sourceLocalClosure W P f) :
    Scheme.Cover.{u} (Scheme.precoverage W) X :=
  hf.choose

lemma property_coverMap_comp {f : X ⟶ Y} (hf : sourceLocalClosure W P f) (i : hf.cover.I₀) :
    P (hf.cover.f i ≫ f) :=
  hf.choose_spec i

lemma le [W.ContainsIdentities] [W.RespectsIso] : P ≤ sourceLocalClosure W P :=
  fun X Y f hf ↦ ⟨X.coverOfIsIso (𝟙 X), by simpa⟩

lemma iff_forall_exists [P.RespectsIso] {f : X ⟶ Y} :
    sourceLocalClosure IsOpenImmersion P f ↔ ∀ (x : X), ∃ (U : X.Opens), x ∈ U ∧ P (U.ι ≫ f) := by
  refine ⟨fun ⟨𝒰, hf⟩ x ↦ ?_, fun H ↦ ?_⟩
  · refine ⟨(𝒰.f (𝒰.idx x)).opensRange, 𝒰.covers x, ?_⟩
    rw [← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc, P.cancel_left_of_respectsIso]
    apply hf
  · choose U hx hf using H
    exact ⟨.mkOfCovers X (fun x ↦ U x) (fun _ ↦ (U _).ι) (fun x ↦ ⟨x, ⟨x, hx x⟩, rfl⟩)
      fun _ ↦ inferInstance, hf⟩

variable [W.IsStableUnderBaseChange] [Scheme.IsJointlySurjectivePreserving W]

-- INSTANCE (free from Core): [P.RespectsLeft

-- INSTANCE (free from Core): [P.RespectsRight

-- INSTANCE (free from Core): [P.RespectsIso]

-- INSTANCE (free from Core): [P.RespectsIso]

-- INSTANCE (free from Core): [P.IsStableUnderBaseChange]

-- INSTANCE (free from Core): [W.ContainsIdentities]

-- INSTANCE (free from Core): [W.IsStableUnderComposition]

-- INSTANCE (free from Core): [W.IsMultiplicative]

end sourceLocalClosure

end AlgebraicGeometry
