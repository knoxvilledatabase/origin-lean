/-
Extracted from CategoryTheory/Monoidal/CommMon_.lean
Genuine: 14 of 33 | Dissolved: 0 | Infrastructure: 19
-/
import Origin.Core
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.Mon_

/-!
# The category of commutative monoids in a braided monoidal category.
-/

universe v₁ v₂ u₁ u₂ u

open CategoryTheory MonoidalCategory

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory.{v₁} C] [BraidedCategory.{v₁} C]

structure CommMon_ extends Mon_ C where
  mul_comm : (β_ _ _).hom ≫ mul = mul := by aesop_cat

attribute [reassoc (attr := simp)] CommMon_.mul_comm

namespace CommMon_

@[simps!]
def trivial : CommMon_ C :=
  { Mon_.trivial C with mul_comm := by dsimp; rw [braiding_leftUnitor, unitors_equal] }

instance : Inhabited (CommMon_ C) :=
  ⟨trivial C⟩

variable {C}

variable {M : CommMon_ C}

instance : Category (CommMon_ C) :=
  InducedCategory.category CommMon_.toMon_

@[simp]
theorem id_hom (A : CommMon_ C) : Mon_.Hom.hom (𝟙 A) = 𝟙 A.X :=
  rfl

@[simp]
theorem comp_hom {R S T : CommMon_ C} (f : R ⟶ S) (g : S ⟶ T) :
    Mon_.Hom.hom (f ≫ g) = f.hom ≫ g.hom :=
  rfl

@[ext]
lemma hom_ext {A B : CommMon_ C} (f g : A ⟶ B) (h : f.hom = g.hom) : f = g :=
  Mon_.Hom.ext h

@[simp]
lemma id' (A : CommMon_ C) : (𝟙 A : A.toMon_ ⟶ A.toMon_) = 𝟙 (A.toMon_) := rfl

@[simp]
lemma comp' {A₁ A₂ A₃ : CommMon_ C} (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃) :
    ((f ≫ g : A₁ ⟶ A₃) : A₁.toMon_ ⟶ A₃.toMon_) = @CategoryStruct.comp (Mon_ C) _ _ _ _ f g := rfl

section

variable (C)

def forget₂Mon_ : CommMon_ C ⥤ Mon_ C :=
  inducedFunctor CommMon_.toMon_

def fullyFaithfulForget₂Mon_ : (forget₂Mon_ C).FullyFaithful :=
  fullyFaithfulInducedFunctor _

instance : (forget₂Mon_ C).Full := InducedCategory.full _

instance : (forget₂Mon_ C).Faithful := InducedCategory.faithful _

@[simp]
theorem forget₂_Mon_obj_one (A : CommMon_ C) : ((forget₂Mon_ C).obj A).one = A.one :=
  rfl

@[simp]
theorem forget₂_Mon_obj_mul (A : CommMon_ C) : ((forget₂Mon_ C).obj A).mul = A.mul :=
  rfl

@[simp]
theorem forget₂_Mon_map_hom {A B : CommMon_ C} (f : A ⟶ B) : ((forget₂Mon_ C).map f).hom = f.hom :=
  rfl

end

section

variable {M N : CommMon_ C} (f : M.X ≅ N.X) (one_f : M.one ≫ f.hom = N.one := by aesop_cat)
  (mul_f : M.mul ≫ f.hom = (f.hom ⊗ f.hom) ≫ N.mul := by aesop_cat)

def mkIso : M ≅ N :=
  (fullyFaithfulForget₂Mon_ C).preimageIso (Mon_.mkIso f one_f mul_f)

@[simp] lemma mkIso_hom_hom : (mkIso f one_f mul_f).hom.hom = f.hom := rfl

@[simp] lemma mkIso_inv_hom : (mkIso f one_f mul_f).inv.hom = f.inv := rfl

end

instance uniqueHomFromTrivial (A : CommMon_ C) : Unique (trivial C ⟶ A) :=
  Mon_.uniqueHomFromTrivial A.toMon_

open CategoryTheory.Limits

instance : HasInitial (CommMon_ C) :=
  hasInitial_of_unique (trivial C)

end CommMon_

namespace CategoryTheory.Functor

variable {C} {D : Type u₂} [Category.{v₂} D] [MonoidalCategory.{v₂} D] [BraidedCategory.{v₂} D]

@[simps!]
def mapCommMon (F : C ⥤ D) [F.LaxBraided] : CommMon_ C ⥤ CommMon_ D where
  obj A :=
    { F.mapMon.obj A.toMon_ with
      mul_comm := by
        dsimp
        rw [← Functor.LaxBraided.braided_assoc, ← Functor.map_comp, A.mul_comm] }
  map f := F.mapMon.map f

variable (C) (D)

@[simps]
def mapCommMonFunctor : LaxBraidedFunctor C D ⥤ CommMon_ C ⥤ CommMon_ D where
  obj F := F.mapCommMon
  map α := { app := fun A => { hom := α.hom.app A.X } }
  map_comp _ _ := rfl

end CategoryTheory.Functor

namespace CommMon_

open CategoryTheory.LaxBraidedFunctor

namespace EquivLaxBraidedFunctorPUnit

@[simps]
def laxBraidedToCommMon : LaxBraidedFunctor (Discrete PUnit.{u + 1}) C ⥤ CommMon_ C where
  obj F := (F.mapCommMon : CommMon_ _ ⥤ CommMon_ C).obj (trivial (Discrete PUnit.{u+1}))
  map α := ((Functor.mapCommMonFunctor (Discrete PUnit) C).map α).app _

variable {C}

@[simps!]
def commMonToLaxBraidedObj (A : CommMon_ C) :
    Discrete PUnit.{u + 1} ⥤ C := (Functor.const _).obj A.X

instance (A : CommMon_ C) : (commMonToLaxBraidedObj A).LaxMonoidal where
  ε' := A.one
  μ' := fun _ _ => A.mul

open Functor.LaxMonoidal

@[simp]
lemma commMonToLaxBraidedObj_ε (A : CommMon_ C) :
    ε (commMonToLaxBraidedObj A) = A.one := rfl

@[simp]
lemma commMonToLaxBraidedObj_μ (A : CommMon_ C) (X Y) :
    μ (commMonToLaxBraidedObj A) X Y = A.mul := rfl

instance (A : CommMon_ C) : (commMonToLaxBraidedObj A).LaxBraided where

variable (C)

@[simps]
def commMonToLaxBraided : CommMon_ C ⥤ LaxBraidedFunctor (Discrete PUnit.{u + 1}) C where
  obj A := LaxBraidedFunctor.of (commMonToLaxBraidedObj A)
  map f :=
    { hom := { app := fun _ => f.hom }
      isMonoidal := { } }

@[simps!]
def unitIso :
    𝟭 (LaxBraidedFunctor (Discrete PUnit.{u + 1}) C) ≅
        laxBraidedToCommMon C ⋙ commMonToLaxBraided C :=
  NatIso.ofComponents
    (fun F ↦ LaxBraidedFunctor.isoOfComponents (fun _ ↦ F.mapIso (eqToIso (by ext))))
    (fun f ↦ by ext ⟨⟨⟩⟩; dsimp; simp)

@[simps!]
def counitIso : commMonToLaxBraided C ⋙ laxBraidedToCommMon C ≅ 𝟭 (CommMon_ C) :=
  NatIso.ofComponents (fun F ↦ mkIso (Iso.refl _))

end EquivLaxBraidedFunctorPUnit

open EquivLaxBraidedFunctorPUnit

@[simps]
def equivLaxBraidedFunctorPUnit : LaxBraidedFunctor (Discrete PUnit.{u + 1}) C ≌ CommMon_ C where
  functor := laxBraidedToCommMon C
  inverse := commMonToLaxBraided C
  unitIso := unitIso C
  counitIso := counitIso C

end CommMon_
