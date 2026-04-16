/-
Extracted from CategoryTheory/Closed/Monoidal.lean
Genuine: 43 | Conflates: 0 | Dissolved: 0 | Infrastructure: 11
-/
import Origin.Core
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Adjunction.Mates

noncomputable section

/-!
# Closed monoidal categories

Define (right) closed objects and (right) closed monoidal categories.

## TODO
Some of the theorems proved about cartesian closed categories
should be generalised and moved to this file.
-/

universe v u u₂ v₂

namespace CategoryTheory

open Category MonoidalCategory

class Closed {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] (X : C) where
  /-- a choice of a right adjoint for `tensorLeft X` -/
  rightAdj : C ⥤ C
  /-- `tensorLeft X` is a left adjoint -/
  adj : tensorLeft X ⊣ rightAdj

class MonoidalClosed (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C] where
  closed (X : C) : Closed X := by infer_instance

attribute [instance 100] MonoidalClosed.closed

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]

def tensorClosed {X Y : C} (hX : Closed X) (hY : Closed Y) : Closed (X ⊗ Y) where
  adj := (hY.adj.comp hX.adj).ofNatIsoLeft (MonoidalCategory.tensorLeftTensor X Y).symm

def unitClosed : Closed (𝟙_ C) where
  rightAdj := 𝟭 C
  adj := Adjunction.id.ofNatIsoLeft (MonoidalCategory.leftUnitorNatIso C).symm

variable (A B : C) {X X' Y Y' Z : C}

variable [Closed A]

def ihom : C ⥤ C :=
  Closed.rightAdj (X := A)

namespace ihom

def adjunction : tensorLeft A ⊣ ihom A :=
  Closed.adj

def ev : ihom A ⋙ tensorLeft A ⟶ 𝟭 C :=
  (ihom.adjunction A).counit

def coev : 𝟭 C ⟶ tensorLeft A ⋙ ihom A :=
  (ihom.adjunction A).unit

@[simp]
theorem ihom_adjunction_counit : (ihom.adjunction A).counit = ev A :=
  rfl

@[simp]
theorem ihom_adjunction_unit : (ihom.adjunction A).unit = coev A :=
  rfl

@[reassoc (attr := simp)]
theorem ev_naturality {X Y : C} (f : X ⟶ Y) :
    A ◁ (ihom A).map f ≫ (ev A).app Y = (ev A).app X ≫ f :=
  (ev A).naturality f

@[reassoc (attr := simp)]
theorem coev_naturality {X Y : C} (f : X ⟶ Y) :
    f ≫ (coev A).app Y = (coev A).app X ≫ (ihom A).map (A ◁ f) :=
  (coev A).naturality f

set_option quotPrecheck false in
/-- `A ⟶[C] B` denotes the internal hom from `A` to `B` -/

notation A " ⟶[" C "] " B:10 => (@ihom C _ _ A _).obj B

@[reassoc (attr := simp)]
theorem ev_coev : (A ◁ (coev A).app B) ≫ (ev A).app (A ⊗ B) = 𝟙 (A ⊗ B) :=
  (ihom.adjunction A).left_triangle_components _

@[reassoc (attr := simp)]
theorem coev_ev : (coev A).app (A ⟶[C] B) ≫ (ihom A).map ((ev A).app B) = 𝟙 (A ⟶[C] B) :=
  Adjunction.right_triangle_components (ihom.adjunction A) _

end ihom

open CategoryTheory.Limits

instance : PreservesColimits (tensorLeft A) :=
  (ihom.adjunction A).leftAdjoint_preservesColimits

variable {A}

namespace MonoidalClosed

def curry : (A ⊗ Y ⟶ X) → (Y ⟶ A ⟶[C] X) :=
  (ihom.adjunction A).homEquiv _ _

def uncurry : (Y ⟶ A ⟶[C] X) → (A ⊗ Y ⟶ X) :=
  ((ihom.adjunction A).homEquiv _ _).symm

@[simp, nolint simpNF]
theorem homEquiv_apply_eq (f : A ⊗ Y ⟶ X) : (ihom.adjunction A).homEquiv _ _ f = curry f :=
  rfl

@[simp, nolint simpNF]
theorem homEquiv_symm_apply_eq (f : Y ⟶ A ⟶[C] X) :
    ((ihom.adjunction A).homEquiv _ _).symm f = uncurry f :=
  rfl

@[reassoc]
theorem curry_natural_left (f : X ⟶ X') (g : A ⊗ X' ⟶ Y) : curry (_ ◁ f ≫ g) = f ≫ curry g :=
  Adjunction.homEquiv_naturality_left _ _ _

@[reassoc]
theorem curry_natural_right (f : A ⊗ X ⟶ Y) (g : Y ⟶ Y') :
    curry (f ≫ g) = curry f ≫ (ihom _).map g :=
  Adjunction.homEquiv_naturality_right _ _ _

@[reassoc]
theorem uncurry_natural_right (f : X ⟶ A ⟶[C] Y) (g : Y ⟶ Y') :
    uncurry (f ≫ (ihom _).map g) = uncurry f ≫ g :=
  Adjunction.homEquiv_naturality_right_symm _ _ _

@[reassoc]
theorem uncurry_natural_left (f : X ⟶ X') (g : X' ⟶ A ⟶[C] Y) :
    uncurry (f ≫ g) = _ ◁ f ≫ uncurry g :=
  Adjunction.homEquiv_naturality_left_symm _ _ _

@[simp]
theorem uncurry_curry (f : A ⊗ X ⟶ Y) : uncurry (curry f) = f :=
  (Closed.adj.homEquiv _ _).left_inv f

@[simp]
theorem curry_uncurry (f : X ⟶ A ⟶[C] Y) : curry (uncurry f) = f :=
  (Closed.adj.homEquiv _ _).right_inv f

theorem curry_eq_iff (f : A ⊗ Y ⟶ X) (g : Y ⟶ A ⟶[C] X) : curry f = g ↔ f = uncurry g :=
  Adjunction.homEquiv_apply_eq (ihom.adjunction A) f g

theorem eq_curry_iff (f : A ⊗ Y ⟶ X) (g : Y ⟶ A ⟶[C] X) : g = curry f ↔ uncurry g = f :=
  Adjunction.eq_homEquiv_apply (ihom.adjunction A) f g

theorem uncurry_eq (g : Y ⟶ A ⟶[C] X) : uncurry g = (A ◁ g) ≫ (ihom.ev A).app X := by
  rfl

theorem curry_eq (g : A ⊗ Y ⟶ X) : curry g = (ihom.coev A).app Y ≫ (ihom A).map g :=
  rfl

theorem curry_injective : Function.Injective (curry : (A ⊗ Y ⟶ X) → (Y ⟶ A ⟶[C] X)) :=
  (Closed.adj.homEquiv _ _).injective

theorem uncurry_injective : Function.Injective (uncurry : (Y ⟶ A ⟶[C] X) → (A ⊗ Y ⟶ X)) :=
  (Closed.adj.homEquiv _ _).symm.injective

variable (A X)

theorem uncurry_id_eq_ev : uncurry (𝟙 (A ⟶[C] X)) = (ihom.ev A).app X := by
  simp [uncurry_eq]

theorem curry_id_eq_coev : curry (𝟙 _) = (ihom.coev A).app X := by
  rw [curry_eq, (ihom A).map_id (A ⊗ _)]
  apply comp_id

def unitNatIso [Closed (𝟙_ C)] : 𝟭 C ≅ ihom (𝟙_ C) :=
  conjugateIsoEquiv (Adjunction.id (C := C)) (ihom.adjunction (𝟙_ C))
    (leftUnitorNatIso C)

section Pre

variable {A B}

variable [Closed B]

def pre (f : B ⟶ A) : ihom A ⟶ ihom B :=
  conjugateEquiv (ihom.adjunction _) (ihom.adjunction _) ((tensoringLeft C).map f)

@[reassoc (attr := simp)]
theorem id_tensor_pre_app_comp_ev (f : B ⟶ A) (X : C) :
    B ◁ (pre f).app X ≫ (ihom.ev B).app X = f ▷ (A ⟶[C] X) ≫ (ihom.ev A).app X :=
  conjugateEquiv_counit _ _ ((tensoringLeft C).map f) X

@[simp]
theorem uncurry_pre (f : B ⟶ A) (X : C) :
    MonoidalClosed.uncurry ((pre f).app X) = f ▷ _ ≫ (ihom.ev A).app X := by
  simp [uncurry_eq]

@[reassoc (attr := simp)]
theorem coev_app_comp_pre_app (f : B ⟶ A) :
    (ihom.coev A).app X ≫ (pre f).app (A ⊗ X) = (ihom.coev B).app X ≫ (ihom B).map (f ▷ _) :=
  unit_conjugateEquiv _ _ ((tensoringLeft C).map f) X

@[simp]
theorem pre_id (A : C) [Closed A] : pre (𝟙 A) = 𝟙 _ := by
  rw [pre, Functor.map_id]
  apply conjugateEquiv_id

@[simp]
theorem pre_map {A₁ A₂ A₃ : C} [Closed A₁] [Closed A₂] [Closed A₃] (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃) :
    pre (f ≫ g) = pre g ≫ pre f := by
  rw [pre, pre, pre, conjugateEquiv_comp, (tensoringLeft C).map_comp]

end Pre

@[simps]
def internalHom [MonoidalClosed C] : Cᵒᵖ ⥤ C ⥤ C where
  obj X := ihom X.unop
  map f := pre f.unop

section OfEquiv

variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory.{v₂} D]

variable (F : C ⥤ D) {G : D ⥤ C} (adj : F ⊣ G)
  [F.Monoidal] [F.IsEquivalence] [MonoidalClosed D]

noncomputable def ofEquiv : MonoidalClosed C where
  closed X :=
    { rightAdj := F ⋙ ihom (F.obj X) ⋙ G
      adj := (adj.comp ((ihom.adjunction (F.obj X)).comp
          adj.toEquivalence.symm.toAdjunction)).ofNatIsoLeft
            (Iso.compInverseIso (H := adj.toEquivalence) (Functor.Monoidal.commTensorLeft F X)) }

theorem ofEquiv_curry_def {X Y Z : C} (f : X ⊗ Y ⟶ Z) :
    letI := ofEquiv F adj
    MonoidalClosed.curry f =
      adj.homEquiv Y ((ihom (F.obj X)).obj (F.obj Z))
        (MonoidalClosed.curry (adj.toEquivalence.symm.toAdjunction.homEquiv (F.obj X ⊗ F.obj Y) Z
        ((Iso.compInverseIso (H := adj.toEquivalence)
          (Functor.Monoidal.commTensorLeft F X)).hom.app Y ≫ f))) := by
  -- This whole proof used to be `rfl` before https://github.com/leanprover-community/mathlib4/pull/16317.
  change ((adj.comp ((ihom.adjunction (F.obj X)).comp
      adj.toEquivalence.symm.toAdjunction)).ofNatIsoLeft _).homEquiv _ _ _ = _
  dsimp only [Adjunction.ofNatIsoLeft]
  rw [Adjunction.mkOfHomEquiv_homEquiv]
  dsimp
  rw [Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
  rfl

theorem ofEquiv_uncurry_def {X Y Z : C} :
    letI := ofEquiv F adj
    ∀ (f : Y ⟶ (ihom X).obj Z), MonoidalClosed.uncurry f =
      ((Iso.compInverseIso (H := adj.toEquivalence)
          (Functor.Monoidal.commTensorLeft F X)).inv.app Y) ≫
            (adj.toEquivalence.symm.toAdjunction.homEquiv _ _).symm
              (MonoidalClosed.uncurry ((adj.homEquiv _ _).symm f)) := by
  intro f
  -- This whole proof used to be `rfl` before https://github.com/leanprover-community/mathlib4/pull/16317.
  change (((adj.comp ((ihom.adjunction (F.obj X)).comp
      adj.toEquivalence.symm.toAdjunction)).ofNatIsoLeft _).homEquiv _ _).symm _ = _
  dsimp only [Adjunction.ofNatIsoLeft]
  rw [Adjunction.mkOfHomEquiv_homEquiv]
  dsimp
  rw [Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
  rfl

end OfEquiv

section Enriched

def id (x : C) [Closed x] : 𝟙_ C ⟶ (ihom x).obj x := curry (ρ_ x).hom

def compTranspose (x y z : C) [Closed x] [Closed y] : x ⊗ (ihom x).obj y ⊗ (ihom y).obj z ⟶ z :=
  (α_ x ((ihom x).obj y) ((ihom y).obj z)).inv ≫
    (ihom.ev x).app y ▷ ((ihom y).obj z) ≫ (ihom.ev y).app z

def comp (x y z : C) [Closed x] [Closed y] : (ihom x).obj y ⊗ (ihom y).obj z ⟶ (ihom x).obj z :=
  curry (compTranspose x y z)

lemma id_eq (x : C) [Closed x] : id x = curry (ρ_ x).hom := rfl

lemma compTranspose_eq (x y z : C) [Closed x] [Closed y] :
    compTranspose x y z = (α_ _ _ _).inv ≫ (ihom.ev x).app y ▷ _ ≫ (ihom.ev y).app z :=
  rfl

lemma comp_eq (x y z : C) [Closed x] [Closed y] : comp x y z = curry (compTranspose x y z) := rfl

/-!
The proofs of associativity and unitality use the following outline:
  1. Take adjoint transpose on each side of the equality (uncurry_injective)
  2. Do whatever rewrites/simps are necessary to apply uncurry_curry
  3. Conclude with simp
-/

@[reassoc (attr := simp)]
lemma id_comp (x y : C) [Closed x] :
    (λ_ ((ihom x).obj y)).inv ≫ id x ▷ _ ≫ comp x x y = 𝟙 _:= by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_natural_left, comp_eq, uncurry_curry, id_eq, compTranspose_eq,
      associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc, ← uncurry_eq,
      uncurry_curry, triangle_assoc_comp_right_assoc, whiskerLeft_inv_hom_assoc,
      uncurry_id_eq_ev _ _]

@[reassoc (attr := simp)]
lemma comp_id (x y : C) [Closed x] [Closed y] :
    (ρ_ ((ihom x).obj y)).inv ≫ _ ◁ id y ≫ comp x y y = 𝟙 _ := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_natural_left, comp_eq, uncurry_curry, compTranspose_eq,
    associator_inv_naturality_right_assoc, ← rightUnitor_tensor_inv_assoc,
    whisker_exchange_assoc, ← rightUnitor_inv_naturality_assoc, ← uncurry_id_eq_ev y y]
  simp only [Functor.id_obj]
  rw [← uncurry_natural_left]
  simp [id_eq, uncurry_id_eq_ev]

@[reassoc]
lemma assoc (w x y z : C) [Closed w] [Closed x] [Closed y] :
    (α_ _ _ _).inv ≫ comp w x y ▷ _ ≫ comp w y z = _ ◁ comp x y z ≫ comp w x z := by
  apply uncurry_injective
  simp only [uncurry_natural_left, comp_eq]
  rw [uncurry_curry, uncurry_curry]; simp only [compTranspose_eq, Category.assoc]
  rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc]; dsimp
  rw [← uncurry_eq, uncurry_curry, associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    ← uncurry_eq, uncurry_curry]
  simp only [comp_whiskerRight, tensorLeft_obj, Category.assoc, pentagon_inv_assoc,
    whiskerRight_tensor, Iso.hom_inv_id_assoc]

end Enriched

end MonoidalClosed

attribute [nolint simpNF] CategoryTheory.MonoidalClosed.homEquiv_apply_eq
  CategoryTheory.MonoidalClosed.homEquiv_symm_apply_eq

end CategoryTheory
