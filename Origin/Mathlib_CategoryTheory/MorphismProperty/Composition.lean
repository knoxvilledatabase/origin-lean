/-
Extracted from CategoryTheory/MorphismProperty/Composition.lean
Genuine: 13 of 24 | Dissolved: 0 | Infrastructure: 11
-/
import Origin.Core

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

-- INSTANCE (free from Core): op

-- INSTANCE (free from Core): unop

lemma of_op (W : MorphismProperty C) [W.op.ContainsIdentities] :
    W.ContainsIdentities := (inferInstance : W.op.unop.ContainsIdentities)

lemma of_unop (W : MorphismProperty Cᵒᵖ) [W.unop.ContainsIdentities] :
    W.ContainsIdentities := (inferInstance : W.unop.op.ContainsIdentities)

lemma eqToHom (W : MorphismProperty C) [W.ContainsIdentities] {x y : C} (h : x = y) :
    W (eqToHom h) := by
  subst h
  rw [eqToHom_refl]
  exact id_mem x

-- INSTANCE (free from Core): inverseImage

-- INSTANCE (free from Core): inf

end ContainsIdentities

-- INSTANCE (free from Core): Prod.containsIdentities

-- INSTANCE (free from Core): Pi.containsIdentities

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

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): IsStableUnderComposition.op

-- INSTANCE (free from Core): IsStableUnderComposition.unop

-- INSTANCE (free from Core): IsStableUnderComposition.inf

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

-- INSTANCE (free from Core): IsStableUnderComposition.inverseImage
