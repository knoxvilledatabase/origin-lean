/-
Extracted from CategoryTheory/Limits/Shapes/IsTerminal.lean
Genuine: 54 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.CategoryTheory.PEmpty
import Mathlib.CategoryTheory.Limits.IsLimit
import Mathlib.CategoryTheory.EpiMono
import Mathlib.CategoryTheory.Category.Preorder

noncomputable section

/-!
# Initial and terminal objects in a category.

In this file we define the predicates `IsTerminal` and `IsInitial` as well as the class
`InitialMonoClass`.

The classes `HasTerminal` and `HasInitial` and the associated notations for terminal and inital
objects are defined in `Terminal.lean`.

## References
* [Stacks: Initial and final objects](https://stacks.math.columbia.edu/tag/002B)
-/

noncomputable section

universe w w' v v₁ v₂ u u₁ u₂

open CategoryTheory

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C]

@[simps]
def asEmptyCone (X : C) : Cone (Functor.empty.{0} C) :=
  { pt := X
    π :=
    { app := by aesop_cat } }

@[simps]
def asEmptyCocone (X : C) : Cocone (Functor.empty.{0} C) :=
  { pt := X
    ι :=
    { app := by aesop_cat } }

abbrev IsTerminal (X : C) :=
  IsLimit (asEmptyCone X)

abbrev IsInitial (X : C) :=
  IsColimit (asEmptyCocone X)

def isTerminalEquivUnique (F : Discrete.{0} PEmpty.{1} ⥤ C) (Y : C) :
    IsLimit (⟨Y, by aesop_cat, by aesop_cat⟩ : Cone F) ≃ ∀ X : C, Unique (X ⟶ Y) where
  toFun t X :=
    { default := t.lift ⟨X, ⟨by aesop_cat, by aesop_cat⟩⟩
      uniq := fun f =>
        t.uniq ⟨X, ⟨by aesop_cat, by aesop_cat⟩⟩ f (by aesop_cat) }
  invFun u :=
    { lift := fun s => (u s.pt).default
      uniq := fun s _ _ => (u s.pt).2 _ }
  left_inv := by dsimp [Function.LeftInverse]; intro x; simp only [eq_iff_true_of_subsingleton]
  right_inv := by
    dsimp [Function.RightInverse,Function.LeftInverse]
    intro u; funext X; simp only

def IsTerminal.ofUnique (Y : C) [h : ∀ X : C, Unique (X ⟶ Y)] : IsTerminal Y where
  lift s := (h s.pt).default
  fac := fun _ ⟨j⟩ => j.elim

def IsTerminal.ofUniqueHom {Y : C} (h : ∀ X : C, X ⟶ Y) (uniq : ∀ (X : C) (m : X ⟶ Y), m = h X) :
    IsTerminal Y :=
  have : ∀ X : C, Unique (X ⟶ Y) := fun X ↦ ⟨⟨h X⟩, uniq X⟩
  IsTerminal.ofUnique Y

def isTerminalTop {α : Type*} [Preorder α] [OrderTop α] : IsTerminal (⊤ : α) :=
  IsTerminal.ofUnique _

def IsTerminal.ofIso {Y Z : C} (hY : IsTerminal Y) (i : Y ≅ Z) : IsTerminal Z :=
  IsLimit.ofIsoLimit hY
    { hom := { hom := i.hom }
      inv := { hom := i.inv } }

def IsTerminal.equivOfIso {X Y : C} (e : X ≅ Y) :
    IsTerminal X ≃ IsTerminal Y where
  toFun h := IsTerminal.ofIso h e
  invFun h := IsTerminal.ofIso h e.symm
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

def isInitialEquivUnique (F : Discrete.{0} PEmpty.{1} ⥤ C) (X : C) :
    IsColimit (⟨X, ⟨by aesop_cat, by aesop_cat⟩⟩ : Cocone F) ≃ ∀ Y : C, Unique (X ⟶ Y) where
  toFun t X :=
    { default := t.desc ⟨X, ⟨by aesop_cat, by aesop_cat⟩⟩
      uniq := fun f => t.uniq ⟨X, ⟨by aesop_cat, by aesop_cat⟩⟩ f (by aesop_cat) }
  invFun u :=
    { desc := fun s => (u s.pt).default
      uniq := fun s _ _ => (u s.pt).2 _ }
  left_inv := by dsimp [Function.LeftInverse]; intro; simp only [eq_iff_true_of_subsingleton]
  right_inv := by
    dsimp [Function.RightInverse,Function.LeftInverse]
    intro; funext; simp only

def IsInitial.ofUnique (X : C) [h : ∀ Y : C, Unique (X ⟶ Y)] : IsInitial X where
  desc s := (h s.pt).default
  fac := fun _ ⟨j⟩ => j.elim

def IsInitial.ofUniqueHom {X : C} (h : ∀ Y : C, X ⟶ Y) (uniq : ∀ (Y : C) (m : X ⟶ Y), m = h Y) :
    IsInitial X :=
  have : ∀ Y : C, Unique (X ⟶ Y) := fun Y ↦ ⟨⟨h Y⟩, uniq Y⟩
  IsInitial.ofUnique X

def isInitialBot {α : Type*} [Preorder α] [OrderBot α] : IsInitial (⊥ : α) :=
  IsInitial.ofUnique _

def IsInitial.ofIso {X Y : C} (hX : IsInitial X) (i : X ≅ Y) : IsInitial Y :=
  IsColimit.ofIsoColimit hX
    { hom := { hom := i.hom }
      inv := { hom := i.inv } }

def IsInitial.equivOfIso {X Y : C} (e : X ≅ Y) :
    IsInitial X ≃ IsInitial Y where
  toFun h := IsInitial.ofIso h e
  invFun h := IsInitial.ofIso h e.symm
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

def IsTerminal.from {X : C} (t : IsTerminal X) (Y : C) : Y ⟶ X :=
  t.lift (asEmptyCone Y)

theorem IsTerminal.hom_ext {X Y : C} (t : IsTerminal X) (f g : Y ⟶ X) : f = g :=
  IsLimit.hom_ext t (by aesop_cat)

@[simp]
theorem IsTerminal.comp_from {Z : C} (t : IsTerminal Z) {X Y : C} (f : X ⟶ Y) :
    f ≫ t.from Y = t.from X :=
  t.hom_ext _ _

@[simp]
theorem IsTerminal.from_self {X : C} (t : IsTerminal X) : t.from X = 𝟙 X :=
  t.hom_ext _ _

def IsInitial.to {X : C} (t : IsInitial X) (Y : C) : X ⟶ Y :=
  t.desc (asEmptyCocone Y)

theorem IsInitial.hom_ext {X Y : C} (t : IsInitial X) (f g : X ⟶ Y) : f = g :=
  IsColimit.hom_ext t (by aesop_cat)

@[simp]
theorem IsInitial.to_comp {X : C} (t : IsInitial X) {Y Z : C} (f : Y ⟶ Z) : t.to Y ≫ f = t.to Z :=
  t.hom_ext _ _

@[simp]
theorem IsInitial.to_self {X : C} (t : IsInitial X) : t.to X = 𝟙 X :=
  t.hom_ext _ _

theorem IsTerminal.isSplitMono_from {X Y : C} (t : IsTerminal X) (f : X ⟶ Y) : IsSplitMono f :=
  IsSplitMono.mk' ⟨t.from _, t.hom_ext _ _⟩

theorem IsInitial.isSplitEpi_to {X Y : C} (t : IsInitial X) (f : Y ⟶ X) : IsSplitEpi f :=
  IsSplitEpi.mk' ⟨t.to _, t.hom_ext _ _⟩

theorem IsTerminal.mono_from {X Y : C} (t : IsTerminal X) (f : X ⟶ Y) : Mono f := by
  haveI := t.isSplitMono_from f; infer_instance

theorem IsInitial.epi_to {X Y : C} (t : IsInitial X) (f : Y ⟶ X) : Epi f := by
  haveI := t.isSplitEpi_to f; infer_instance

@[simps]
def IsTerminal.uniqueUpToIso {T T' : C} (hT : IsTerminal T) (hT' : IsTerminal T') : T ≅ T' where
  hom := hT'.from _
  inv := hT.from _

@[simps]
def IsInitial.uniqueUpToIso {I I' : C} (hI : IsInitial I) (hI' : IsInitial I') : I ≅ I' where
  hom := hI.to _
  inv := hI'.to _

variable (C)

section Univ

variable (X : C) {F₁ : Discrete.{w} PEmpty ⥤ C} {F₂ : Discrete.{w'} PEmpty ⥤ C}

def isLimitChangeEmptyCone {c₁ : Cone F₁} (hl : IsLimit c₁) (c₂ : Cone F₂) (hi : c₁.pt ≅ c₂.pt) :
    IsLimit c₂ where
  lift c := hl.lift ⟨c.pt, by aesop_cat, by aesop_cat⟩ ≫ hi.hom
  uniq c f _ := by
    dsimp
    rw [← hl.uniq _ (f ≫ hi.inv) _]
    · simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    · aesop_cat

def isLimitEmptyConeEquiv (c₁ : Cone F₁) (c₂ : Cone F₂) (h : c₁.pt ≅ c₂.pt) :
    IsLimit c₁ ≃ IsLimit c₂ where
  toFun hl := isLimitChangeEmptyCone C hl c₂ h
  invFun hl := isLimitChangeEmptyCone C hl c₁ h.symm
  left_inv := by dsimp [Function.LeftInverse]; intro; simp only [eq_iff_true_of_subsingleton]
  right_inv := by
    dsimp [Function.LeftInverse,Function.RightInverse]; intro
    simp only [eq_iff_true_of_subsingleton]

def isColimitChangeEmptyCocone {c₁ : Cocone F₁} (hl : IsColimit c₁) (c₂ : Cocone F₂)
    (hi : c₁.pt ≅ c₂.pt) : IsColimit c₂ where
  desc c := hi.inv ≫ hl.desc ⟨c.pt, by aesop_cat, by aesop_cat⟩
  uniq c f _ := by
    dsimp
    rw [← hl.uniq _ (hi.hom ≫ f) _]
    · simp only [Iso.inv_hom_id_assoc]
    · aesop_cat

def isColimitEmptyCoconeEquiv (c₁ : Cocone F₁) (c₂ : Cocone F₂) (h : c₁.pt ≅ c₂.pt) :
    IsColimit c₁ ≃ IsColimit c₂ where
  toFun hl := isColimitChangeEmptyCocone C hl c₂ h
  invFun hl := isColimitChangeEmptyCocone C hl c₁ h.symm
  left_inv := by dsimp [Function.LeftInverse]; intro; simp only [eq_iff_true_of_subsingleton]
  right_inv := by
    dsimp [Function.LeftInverse,Function.RightInverse]; intro
    simp only [eq_iff_true_of_subsingleton]

end Univ

section

variable {C}

def terminalOpOfInitial {X : C} (t : IsInitial X) : IsTerminal (Opposite.op X) where
  lift s := (t.to s.pt.unop).op
  uniq _ _ _ := Quiver.Hom.unop_inj (t.hom_ext _ _)

def terminalUnopOfInitial {X : Cᵒᵖ} (t : IsInitial X) : IsTerminal X.unop where
  lift s := (t.to (Opposite.op s.pt)).unop
  uniq _ _ _ := Quiver.Hom.op_inj (t.hom_ext _ _)

def initialOpOfTerminal {X : C} (t : IsTerminal X) : IsInitial (Opposite.op X) where
  desc s := (t.from s.pt.unop).op
  uniq _ _ _ := Quiver.Hom.unop_inj (t.hom_ext _ _)

def initialUnopOfTerminal {X : Cᵒᵖ} (t : IsTerminal X) : IsInitial X.unop where
  desc s := (t.from (Opposite.op s.pt)).unop
  uniq _ _ _ := Quiver.Hom.op_inj (t.hom_ext _ _)

class InitialMonoClass (C : Type u₁) [Category.{v₁} C] : Prop where
  /-- The map from the (any as stated) initial object to any other object is a
    monomorphism -/
  isInitial_mono_from : ∀ {I} (X : C) (hI : IsInitial I), Mono (hI.to X)

theorem IsInitial.mono_from [InitialMonoClass C] {I} {X : C} (hI : IsInitial I) (f : I ⟶ X) :
    Mono f := by
  rw [hI.hom_ext f (hI.to X)]
  apply InitialMonoClass.isInitial_mono_from

theorem InitialMonoClass.of_isInitial {I : C} (hI : IsInitial I) (h : ∀ X, Mono (hI.to X)) :
    InitialMonoClass C where
  isInitial_mono_from {I'} X hI' := by
    rw [hI'.hom_ext (hI'.to X) ((hI'.uniqueUpToIso hI).hom ≫ hI.to X)]
    apply mono_comp

theorem InitialMonoClass.of_isTerminal {I T : C} (hI : IsInitial I) (hT : IsTerminal T)
    (_ : Mono (hI.to T)) : InitialMonoClass C :=
  InitialMonoClass.of_isInitial hI fun X => mono_of_mono_fac (hI.hom_ext (_ ≫ hT.from X) (hI.to T))

section Comparison

variable {D : Type u₂} [Category.{v₂} D] (G : C ⥤ D)

end Comparison

variable {J : Type u} [Category.{v} J]

@[simps]
def coneOfDiagramInitial {X : J} (tX : IsInitial X) (F : J ⥤ C) : Cone F where
  pt := F.obj X
  π :=
    { app := fun j => F.map (tX.to j)
      naturality := fun j j' k => by
        dsimp
        rw [← F.map_comp, Category.id_comp, tX.hom_ext (tX.to j ≫ k) (tX.to j')] }

def limitOfDiagramInitial {X : J} (tX : IsInitial X) (F : J ⥤ C) :
    IsLimit (coneOfDiagramInitial tX F) where
  lift s := s.π.app X
  uniq s m w := by
    conv_lhs => dsimp
    simp_rw [← w X, coneOfDiagramInitial_π_app, tX.hom_ext (tX.to X) (𝟙 _)]
    simp

@[simps]
def coneOfDiagramTerminal {X : J} (hX : IsTerminal X) (F : J ⥤ C)
    [∀ (i j : J) (f : i ⟶ j), IsIso (F.map f)] : Cone F where
  pt := F.obj X
  π :=
    { app := fun _ => inv (F.map (hX.from _))
      naturality := by
        intro i j f
        dsimp
        simp only [IsIso.eq_inv_comp, IsIso.comp_inv_eq, Category.id_comp, ← F.map_comp,
          hX.hom_ext (hX.from i) (f ≫ hX.from j)] }

def limitOfDiagramTerminal {X : J} (hX : IsTerminal X) (F : J ⥤ C)
    [∀ (i j : J) (f : i ⟶ j), IsIso (F.map f)] : IsLimit (coneOfDiagramTerminal hX F) where
  lift S := S.π.app _

@[simps]
def coconeOfDiagramTerminal {X : J} (tX : IsTerminal X) (F : J ⥤ C) : Cocone F where
  pt := F.obj X
  ι :=
    { app := fun j => F.map (tX.from j)
      naturality := fun j j' k => by
        dsimp
        rw [← F.map_comp, Category.comp_id, tX.hom_ext (k ≫ tX.from j') (tX.from j)] }

def colimitOfDiagramTerminal {X : J} (tX : IsTerminal X) (F : J ⥤ C) :
    IsColimit (coconeOfDiagramTerminal tX F) where
  desc s := s.ι.app X
  uniq s m w := by
    conv_rhs => dsimp -- Porting note: why do I need this much firepower?
    rw [← w X, coconeOfDiagramTerminal_ι_app, tX.hom_ext (tX.from X) (𝟙 _)]
    simp

lemma IsColimit.isIso_ι_app_of_isTerminal {F : J ⥤ C} {c : Cocone F} (hc : IsColimit c)
    (X : J) (hX : IsTerminal X) :
    IsIso (c.ι.app X) := by
  change IsIso (coconePointUniqueUpToIso (colimitOfDiagramTerminal hX F) hc).hom
  infer_instance

@[simps]
def coconeOfDiagramInitial {X : J} (hX : IsInitial X) (F : J ⥤ C)
    [∀ (i j : J) (f : i ⟶ j), IsIso (F.map f)] : Cocone F where
  pt := F.obj X
  ι :=
    { app := fun _ => inv (F.map (hX.to _))
      naturality := by
        intro i j f
        dsimp
        simp only [IsIso.eq_inv_comp, IsIso.comp_inv_eq, Category.comp_id, ← F.map_comp,
          hX.hom_ext (hX.to i ≫ f) (hX.to j)] }

def colimitOfDiagramInitial {X : J} (hX : IsInitial X) (F : J ⥤ C)
    [∀ (i j : J) (f : i ⟶ j), IsIso (F.map f)] : IsColimit (coconeOfDiagramInitial hX F) where
  desc S := S.ι.app _

lemma IsLimit.isIso_π_app_of_isInitial {F : J ⥤ C} {c : Cone F} (hc : IsLimit c)
    (X : J) (hX : IsInitial X) :
    IsIso (c.π.app X) := by
  change IsIso (conePointUniqueUpToIso hc (limitOfDiagramInitial hX F)).hom
  infer_instance

lemma isIso_of_isTerminal {X Y : C} (hX : IsTerminal X) (hY : IsTerminal Y) (f : X ⟶ Y) :
    IsIso f := by
  refine ⟨⟨IsTerminal.from hX Y, ?_⟩⟩
  simp only [IsTerminal.comp_from, IsTerminal.from_self, true_and]
  apply IsTerminal.hom_ext hY

lemma isIso_of_isInitial {X Y : C} (hX : IsInitial X) (hY : IsInitial Y) (f : X ⟶ Y) :
    IsIso f := by
  refine ⟨⟨IsInitial.to hY X, ?_⟩⟩
  simp only [IsInitial.to_comp, IsInitial.to_self, and_true]
  apply IsInitial.hom_ext hX

end

end CategoryTheory.Limits
