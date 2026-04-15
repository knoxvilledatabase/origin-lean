/-
Extracted from CategoryTheory/MorphismProperty/Composition.lean
Genuine: 24 of 46 | Dissolved: 0 | Infrastructure: 22
-/
import Origin.Core
import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# Compatibilities of properties of morphisms with respect to composition

Given `P : MorphismProperty C`, we define the predicate `P.IsStableUnderComposition`
which means that `P f → P g → P (f ≫ g)`. We also introduce the type classes
`W.ContainsIdentities`, `W.IsMultiplicative`, and `W.HasTwoOutOfThreeProperty`.

-/

universe w v v' u u'

namespace CategoryTheory

namespace MorphismProperty

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

class ContainsIdentities (W : MorphismProperty C) : Prop where
  /-- for all `X : C`, the identity of `X` satisfies the morphism property -/
  id_mem : ∀ (X : C), W (𝟙 X)

lemma id_mem (W : MorphismProperty C) [W.ContainsIdentities] (X : C) :
    W (𝟙 X) := ContainsIdentities.id_mem X

namespace ContainsIdentities

instance op (W : MorphismProperty C) [W.ContainsIdentities] :
    W.op.ContainsIdentities := ⟨fun X => W.id_mem X.unop⟩

instance unop (W : MorphismProperty Cᵒᵖ) [W.ContainsIdentities] :
    W.unop.ContainsIdentities := ⟨fun X => W.id_mem (Opposite.op X)⟩

lemma of_op (W : MorphismProperty C) [W.op.ContainsIdentities] :
    W.ContainsIdentities := (inferInstance : W.op.unop.ContainsIdentities)

lemma of_unop (W : MorphismProperty Cᵒᵖ) [W.unop.ContainsIdentities] :
    W.ContainsIdentities := (inferInstance : W.unop.op.ContainsIdentities)

instance inverseImage {P : MorphismProperty D} [P.ContainsIdentities] (F : C ⥤ D) :
    (P.inverseImage F).ContainsIdentities where
  id_mem X := by simpa only [← F.map_id] using P.id_mem (F.obj X)

instance inf {P Q : MorphismProperty C} [P.ContainsIdentities] [Q.ContainsIdentities] :
    (P ⊓ Q).ContainsIdentities where
  id_mem X := ⟨P.id_mem X, Q.id_mem X⟩

end ContainsIdentities

instance Prod.containsIdentities {C₁ C₂ : Type*} [Category C₁] [Category C₂]
    (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
    [W₁.ContainsIdentities] [W₂.ContainsIdentities] : (prod W₁ W₂).ContainsIdentities :=
  ⟨fun _ => ⟨W₁.id_mem _, W₂.id_mem _⟩⟩

instance Pi.containsIdentities {J : Type w} {C : J → Type u}
  [∀ j, Category.{v} (C j)] (W : ∀ j, MorphismProperty (C j)) [∀ j, (W j).ContainsIdentities] :
    (pi W).ContainsIdentities :=
  ⟨fun _ _ => MorphismProperty.id_mem _ _⟩

lemma of_isIso (P : MorphismProperty C) [P.ContainsIdentities] [P.RespectsIso] {X Y : C} (f : X ⟶ Y)
    [IsIso f] : P f :=
  Category.id_comp f ▸ RespectsIso.postcomp P f (𝟙 X) (P.id_mem X)

lemma isomorphisms_le_of_containsIdentities (P : MorphismProperty C) [P.ContainsIdentities]
    [P.RespectsIso] :
    isomorphisms C ≤ P := fun _ _ f (_ : IsIso f) ↦ P.of_isIso f

class IsStableUnderComposition (P : MorphismProperty C) : Prop where
  comp_mem {X Y Z} (f : X ⟶ Y) (g : Y ⟶ Z) : P f → P g → P (f ≫ g)

lemma comp_mem (W : MorphismProperty C) [W.IsStableUnderComposition]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) (hg : W g) : W (f ≫ g) :=
  IsStableUnderComposition.comp_mem f g hf hg

instance (priority := 900) (W : MorphismProperty C) [W.IsStableUnderComposition] :
    W.Respects W where
  precomp _ hi _ hf := W.comp_mem _ _ hi hf
  postcomp _ hi _ hf := W.comp_mem _ _ hf hi

instance IsStableUnderComposition.op {P : MorphismProperty C} [P.IsStableUnderComposition] :
    P.op.IsStableUnderComposition where
  comp_mem f g hf hg := P.comp_mem g.unop f.unop hg hf

instance IsStableUnderComposition.unop {P : MorphismProperty Cᵒᵖ} [P.IsStableUnderComposition] :
    P.unop.IsStableUnderComposition where
  comp_mem f g hf hg := P.comp_mem g.op f.op hg hf

instance IsStableUnderComposition.inf {P Q : MorphismProperty C} [P.IsStableUnderComposition]
    [Q.IsStableUnderComposition] :
    (P ⊓ Q).IsStableUnderComposition where
  comp_mem f g hf hg := ⟨P.comp_mem f g hf.left hg.left, Q.comp_mem f g hf.right hg.right⟩

def StableUnderInverse (P : MorphismProperty C) : Prop :=
  ∀ ⦃X Y⦄ (e : X ≅ Y), P e.hom → P e.inv

theorem StableUnderInverse.op {P : MorphismProperty C} (h : StableUnderInverse P) :
    StableUnderInverse P.op := fun _ _ e he => h e.unop he

theorem StableUnderInverse.unop {P : MorphismProperty Cᵒᵖ} (h : StableUnderInverse P) :
    StableUnderInverse P.unop := fun _ _ e he => h e.op he

theorem respectsIso_of_isStableUnderComposition {P : MorphismProperty C}
    [P.IsStableUnderComposition] (hP : isomorphisms C ≤ P) :
    RespectsIso P := RespectsIso.mk _
  (fun _ _ hf => P.comp_mem _ _ (hP _ (isomorphisms.infer_property _)) hf)
    (fun _ _ hf => P.comp_mem _ _ hf (hP _ (isomorphisms.infer_property _)))

instance IsStableUnderComposition.inverseImage {P : MorphismProperty D} [P.IsStableUnderComposition]
    (F : C ⥤ D) : (P.inverseImage F).IsStableUnderComposition where
  comp_mem f g hf hg := by simpa only [← F.map_comp] using P.comp_mem _ _ hf hg

@[simp]
def naturalityProperty {F₁ F₂ : C ⥤ D} (app : ∀ X, F₁.obj X ⟶ F₂.obj X) : MorphismProperty C :=
  fun X Y f => F₁.map f ≫ app Y = app X ≫ F₂.map f

namespace naturalityProperty

instance isStableUnderComposition {F₁ F₂ : C ⥤ D} (app : ∀ X, F₁.obj X ⟶ F₂.obj X) :
    (naturalityProperty app).IsStableUnderComposition where
  comp_mem f g hf hg := by
    simp only [naturalityProperty] at hf hg ⊢
    simp only [Functor.map_comp, Category.assoc, hg]
    slice_lhs 1 2 => rw [hf]
    rw [Category.assoc]

theorem stableUnderInverse {F₁ F₂ : C ⥤ D} (app : ∀ X, F₁.obj X ⟶ F₂.obj X) :
    (naturalityProperty app).StableUnderInverse := fun X Y e he => by
  simp only [naturalityProperty] at he ⊢
  rw [← cancel_epi (F₁.map e.hom)]
  slice_rhs 1 2 => rw [he]
  simp only [Category.assoc, ← F₁.map_comp_assoc, ← F₂.map_comp, e.hom_inv_id, Functor.map_id,
    Category.id_comp, Category.comp_id]

end naturalityProperty

class IsMultiplicative (W : MorphismProperty C)
    extends W.ContainsIdentities, W.IsStableUnderComposition : Prop

namespace IsMultiplicative

instance op (W : MorphismProperty C) [IsMultiplicative W] : IsMultiplicative W.op where
  comp_mem f g hf hg := W.comp_mem g.unop f.unop hg hf

instance unop (W : MorphismProperty Cᵒᵖ) [IsMultiplicative W] : IsMultiplicative W.unop where
  id_mem _ := W.id_mem _
  comp_mem f g hf hg := W.comp_mem g.op f.op hg hf

lemma of_op (W : MorphismProperty C) [IsMultiplicative W.op] : IsMultiplicative W :=
  (inferInstance : IsMultiplicative W.op.unop)

lemma of_unop (W : MorphismProperty Cᵒᵖ) [IsMultiplicative W.unop] : IsMultiplicative W :=
  (inferInstance : IsMultiplicative W.unop.op)

instance : MorphismProperty.IsMultiplicative (⊤ : MorphismProperty C) where
  comp_mem _ _ _ _ := trivial
  id_mem _ := trivial

instance : (isomorphisms C).IsMultiplicative where
  id_mem _ := isomorphisms.infer_property _
  comp_mem f g hf hg := by
    rw [isomorphisms.iff] at hf hg ⊢
    infer_instance

instance : (monomorphisms C).IsMultiplicative where
  id_mem _ := monomorphisms.infer_property _
  comp_mem f g hf hg := by
    rw [monomorphisms.iff] at hf hg ⊢
    apply mono_comp

instance : (epimorphisms C).IsMultiplicative where
  id_mem _ := epimorphisms.infer_property _
  comp_mem f g hf hg := by
    rw [epimorphisms.iff] at hf hg ⊢
    apply epi_comp

instance {P : MorphismProperty D} [P.IsMultiplicative] (F : C ⥤ D) :
    (P.inverseImage F).IsMultiplicative where

instance inf {P Q : MorphismProperty C} [P.IsMultiplicative] [Q.IsMultiplicative] :
    (P ⊓ Q).IsMultiplicative where

end IsMultiplicative

class HasOfPostcompProperty (W W' : MorphismProperty C) : Prop where
  of_postcomp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W' g → W (f ≫ g) → W f

class HasOfPrecompProperty (W W' : MorphismProperty C) : Prop where
  of_precomp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W' f → W (f ≫ g) → W g

class HasTwoOutOfThreeProperty (W : MorphismProperty C)
    extends W.IsStableUnderComposition, W.HasOfPostcompProperty W,
      W.HasOfPrecompProperty W : Prop where

section

variable (W W' : MorphismProperty C) {W'}

lemma of_postcomp [W.HasOfPostcompProperty W'] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hg : W' g)
    (hfg : W (f ≫ g)) : W f :=
  HasOfPostcompProperty.of_postcomp f g hg hfg

lemma of_precomp [W.HasOfPrecompProperty W'] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W' f)
    (hfg : W (f ≫ g)) : W g :=
  HasOfPrecompProperty.of_precomp f g hf hfg

lemma postcomp_iff [W.RespectsRight W'] [W.HasOfPostcompProperty W']
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hg : W' g) : W (f ≫ g) ↔ W f :=
  ⟨W.of_postcomp f g hg, fun hf ↦ RespectsRight.postcomp _ hg _ hf⟩

lemma precomp_iff [W.RespectsLeft W'] [W.HasOfPrecompProperty W']
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W' f) :
    W (f ≫ g) ↔ W g :=
  ⟨W.of_precomp f g hf, fun hg ↦ RespectsLeft.precomp _ hf _ hg⟩

end

instance : (isomorphisms C).HasTwoOutOfThreeProperty where
  of_postcomp f g := fun (hg : IsIso g) (hfg : IsIso (f ≫ g)) =>
    by simpa using (inferInstance : IsIso ((f ≫ g) ≫ inv g))
  of_precomp f g := fun (hf : IsIso f) (hfg : IsIso (f ≫ g)) =>
    by simpa using (inferInstance : IsIso (inv f ≫ (f ≫ g)))

instance (F : C ⥤ D) (W : MorphismProperty D) [W.HasTwoOutOfThreeProperty] :
    (W.inverseImage F).HasTwoOutOfThreeProperty where
  of_postcomp f g hg hfg := W.of_postcomp (F.map f) (F.map g) hg (by simpa using hfg)
  of_precomp f g hf hfg := W.of_precomp (F.map f) (F.map g) hf (by simpa using hfg)

end MorphismProperty

end CategoryTheory
