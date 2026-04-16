/-
Extracted from CategoryTheory/Limits/ExactFunctor.lean
Genuine: 17 | Conflates: 0 | Dissolved: 0 | Infrastructure: 33
-/
import Origin.Core
import Mathlib.CategoryTheory.Limits.Preserves.Finite

noncomputable section

/-!
# Bundled exact functors

We say that a functor `F` is left exact if it preserves finite limits, it is right exact if it
preserves finite colimits, and it is exact if it is both left exact and right exact.

In this file, we define the categories of bundled left exact, right exact and exact functors.

-/

universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

section

variable (C) (D)

def LeftExactFunctor :=
  FullSubcategory fun F : C ⥤ D => PreservesFiniteLimits F

instance : Category (LeftExactFunctor C D) :=
  FullSubcategory.category _

infixr:26 " ⥤ₗ " => LeftExactFunctor

def LeftExactFunctor.forget : (C ⥤ₗ D) ⥤ C ⥤ D :=
  fullSubcategoryInclusion _

instance : (LeftExactFunctor.forget C D).Full :=
  FullSubcategory.full _

instance : (LeftExactFunctor.forget C D).Faithful :=
  FullSubcategory.faithful _

def RightExactFunctor :=
  FullSubcategory fun F : C ⥤ D => PreservesFiniteColimits F

instance : Category (RightExactFunctor C D) :=
  FullSubcategory.category _

infixr:26 " ⥤ᵣ " => RightExactFunctor

def RightExactFunctor.forget : (C ⥤ᵣ D) ⥤ C ⥤ D :=
  fullSubcategoryInclusion _

instance : (RightExactFunctor.forget C D).Full :=
  FullSubcategory.full _

instance : (RightExactFunctor.forget C D).Faithful :=
  FullSubcategory.faithful _

def ExactFunctor :=
  FullSubcategory fun F : C ⥤ D =>
    PreservesFiniteLimits F ∧ PreservesFiniteColimits F

instance : Category (ExactFunctor C D) :=
  FullSubcategory.category _

infixr:26 " ⥤ₑ " => ExactFunctor

def ExactFunctor.forget : (C ⥤ₑ D) ⥤ C ⥤ D :=
  fullSubcategoryInclusion _

instance : (ExactFunctor.forget C D).Full :=
  FullSubcategory.full _

instance : (ExactFunctor.forget C D).Faithful :=
  FullSubcategory.faithful _

def LeftExactFunctor.ofExact : (C ⥤ₑ D) ⥤ C ⥤ₗ D :=
  FullSubcategory.map fun _ => And.left

instance : (LeftExactFunctor.ofExact C D).Full :=
  FullSubcategory.full_map _

instance : (LeftExactFunctor.ofExact C D).Faithful :=
  FullSubcategory.faithful_map _

def RightExactFunctor.ofExact : (C ⥤ₑ D) ⥤ C ⥤ᵣ D :=
  FullSubcategory.map fun _ => And.right

instance : (RightExactFunctor.ofExact C D).Full :=
  FullSubcategory.full_map _

instance : (RightExactFunctor.ofExact C D).Faithful :=
  FullSubcategory.faithful_map _

variable {C D}

def LeftExactFunctor.of (F : C ⥤ D) [PreservesFiniteLimits F] : C ⥤ₗ D :=
  ⟨F, inferInstance⟩

def RightExactFunctor.of (F : C ⥤ D) [PreservesFiniteColimits F] : C ⥤ᵣ D :=
  ⟨F, inferInstance⟩

def ExactFunctor.of (F : C ⥤ D) [PreservesFiniteLimits F] [PreservesFiniteColimits F] : C ⥤ₑ D :=
  ⟨F, ⟨inferInstance, inferInstance⟩⟩

noncomputable instance (F : C ⥤ₗ D) : PreservesFiniteLimits F.obj :=
  F.property

noncomputable instance (F : C ⥤ᵣ D) : PreservesFiniteColimits F.obj :=
  F.property

noncomputable instance (F : C ⥤ₑ D) : PreservesFiniteLimits F.obj :=
  F.property.1

noncomputable instance (F : C ⥤ₑ D) : PreservesFiniteColimits F.obj :=
  F.property.2

variable {E : Type u₃} [Category.{v₃} E]

section

variable (C D E)

@[simps!]
def LeftExactFunctor.whiskeringLeft : (C ⥤ₗ D) ⥤ (D ⥤ₗ E) ⥤ (C ⥤ₗ E) where
  obj F := FullSubcategory.lift _ (forget _ _ ⋙ (CategoryTheory.whiskeringLeft C D E).obj F.obj)
    (fun G => by dsimp; exact comp_preservesFiniteLimits _ _)
  map {F G} η :=
    { app := fun H => ((CategoryTheory.whiskeringLeft C D E).map η).app H.obj
      naturality := fun _ _ f => ((CategoryTheory.whiskeringLeft C D E).map η).naturality f }
  map_id X := by
    rw [FullSubcategory.id_def]
    aesop_cat
  map_comp f g := by
    rw [FullSubcategory.comp_def]
    aesop_cat

@[simps!]
def LeftExactFunctor.whiskeringRight : (D ⥤ₗ E) ⥤ (C ⥤ₗ D) ⥤ (C ⥤ₗ E) where
  obj F := FullSubcategory.lift _ (forget _ _ ⋙ (CategoryTheory.whiskeringRight C D E).obj F.obj)
    (fun G => by dsimp; exact comp_preservesFiniteLimits _ _)
  map {F G} η :=
    { app := fun H => ((CategoryTheory.whiskeringRight C D E).map η).app H.obj
      naturality := fun _ _ f => ((CategoryTheory.whiskeringRight C D E).map η).naturality f }
  map_id X := by
    rw [FullSubcategory.id_def]
    aesop_cat
  map_comp f g := by
    rw [FullSubcategory.comp_def]
    aesop_cat

@[simps!]
def RightExactFunctor.whiskeringLeft : (C ⥤ᵣ D) ⥤ (D ⥤ᵣ E) ⥤ (C ⥤ᵣ E) where
  obj F := FullSubcategory.lift _ (forget _ _ ⋙ (CategoryTheory.whiskeringLeft C D E).obj F.obj)
    (fun G => by dsimp; exact comp_preservesFiniteColimits _ _)
  map {F G} η :=
    { app := fun H => ((CategoryTheory.whiskeringLeft C D E).map η).app H.obj
      naturality := fun _ _ f => ((CategoryTheory.whiskeringLeft C D E).map η).naturality f }
  map_id X := by
    rw [FullSubcategory.id_def]
    aesop_cat
  map_comp f g := by
    rw [FullSubcategory.comp_def]
    aesop_cat

@[simps!]
def RightExactFunctor.whiskeringRight : (D ⥤ᵣ E) ⥤ (C ⥤ᵣ D) ⥤ (C ⥤ᵣ E) where
  obj F := FullSubcategory.lift _ (forget _ _ ⋙ (CategoryTheory.whiskeringRight C D E).obj F.obj)
    (fun G => by dsimp; exact comp_preservesFiniteColimits _ _)
  map {F G} η :=
    { app := fun H => ((CategoryTheory.whiskeringRight C D E).map η).app H.obj
      naturality := fun _ _ f => ((CategoryTheory.whiskeringRight C D E).map η).naturality f }
  map_id X := by
    rw [FullSubcategory.id_def]
    aesop_cat
  map_comp f g := by
    rw [FullSubcategory.comp_def]
    aesop_cat

@[simps!]
def ExactFunctor.whiskeringLeft : (C ⥤ₑ D) ⥤ (D ⥤ₑ E) ⥤ (C ⥤ₑ E) where
  obj F := FullSubcategory.lift _ (forget _ _ ⋙ (CategoryTheory.whiskeringLeft C D E).obj F.obj)
    (fun G => ⟨by dsimp; exact comp_preservesFiniteLimits _ _,
      by dsimp; exact comp_preservesFiniteColimits _ _⟩)
  map {F G} η :=
    { app := fun H => ((CategoryTheory.whiskeringLeft C D E).map η).app H.obj
      naturality := fun _ _ f => ((CategoryTheory.whiskeringLeft C D E).map η).naturality f }
  map_id X := by
    rw [FullSubcategory.id_def]
    aesop_cat
  map_comp f g := by
    rw [FullSubcategory.comp_def]
    aesop_cat

@[simps!]
def ExactFunctor.whiskeringRight : (D ⥤ₑ E) ⥤ (C ⥤ₑ D) ⥤ (C ⥤ₑ E) where
  obj F := FullSubcategory.lift _ (forget _ _ ⋙ (CategoryTheory.whiskeringRight C D E).obj F.obj)
    (fun G => ⟨by dsimp; exact comp_preservesFiniteLimits _ _,
      by dsimp; exact comp_preservesFiniteColimits _ _⟩)
  map {F G} η :=
    { app := fun H => ((CategoryTheory.whiskeringRight C D E).map η).app H.obj
      naturality := fun _ _ f => ((CategoryTheory.whiskeringRight C D E).map η).naturality f }
  map_id X := by
    rw [FullSubcategory.id_def]
    aesop_cat
  map_comp f g := by
    rw [FullSubcategory.comp_def]
    aesop_cat

end

end

end CategoryTheory
