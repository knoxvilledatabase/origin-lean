/-
Extracted from CategoryTheory/Monoidal/Opposite.lean
Genuine: 23 | Conflates: 0 | Dissolved: 0 | Infrastructure: 73
-/
import Origin.Core
import Mathlib.Tactic.CategoryTheory.Monoidal.PureCoherence

noncomputable section

/-!
# Monoidal opposites

We write `Cᵐᵒᵖ` for the monoidal opposite of a monoidal category `C`.
-/

universe v₁ v₂ u₁ u₂

variable {C : Type u₁}

namespace CategoryTheory

open CategoryTheory.MonoidalCategory

structure MonoidalOpposite (C : Type u₁) where
  /-- The object of `MonoidalOpposite C` that represents `x : C`. -/ mop ::
  /-- The object of `C` represented by `x : MonoidalOpposite C`. -/ unmop : C

namespace MonoidalOpposite

notation:max C "ᴹᵒᵖ" => MonoidalOpposite C

theorem mop_injective : Function.Injective (mop : C → Cᴹᵒᵖ) := @mop.inj C

theorem unmop_injective : Function.Injective (unmop : Cᴹᵒᵖ → C) :=
  fun _ _ h => congrArg mop h

theorem mop_inj_iff (x y : C) : mop x = mop y ↔ x = y := mop_injective.eq_iff

@[simp]
theorem unmop_inj_iff (x y : Cᴹᵒᵖ) : unmop x = unmop y ↔ x = y := unmop_injective.eq_iff

instance monoidalOppositeCategory [Category.{v₁} C] : Category Cᴹᵒᵖ where
  Hom X Y := (unmop X ⟶ unmop Y)ᴹᵒᵖ
  id X := mop (𝟙 (unmop X))
  comp f g := mop (unmop f ≫ unmop g)

end MonoidalOpposite

end CategoryTheory

open CategoryTheory

open CategoryTheory.MonoidalOpposite

variable [Category.{v₁} C]

def Quiver.Hom.mop {X Y : C} (f : X ⟶ Y) : mop X ⟶ mop Y := MonoidalOpposite.mop f

def Quiver.Hom.unmop {X Y : Cᴹᵒᵖ} (f : X ⟶ Y) : unmop X ⟶ unmop Y := MonoidalOpposite.unmop f

namespace Quiver.Hom

open MonoidalOpposite renaming mop → mop', unmop → unmop'

theorem mop_inj {X Y : C} :
    Function.Injective (Quiver.Hom.mop : (X ⟶ Y) → (mop' X ⟶ mop' Y)) :=
  fun _ _ H => congr_arg Quiver.Hom.unmop H

theorem unmop_inj {X Y : Cᴹᵒᵖ} :
    Function.Injective (Quiver.Hom.unmop : (X ⟶ Y) → (unmop' X ⟶ unmop' Y)) :=
  fun _ _ H => congr_arg Quiver.Hom.mop H

end Quiver.Hom

namespace CategoryTheory

variable (C)

@[simps obj map] -- need to specify `obj, map` or else we generate `mopFunctor_obj_unmop`
def mopFunctor : C ⥤ Cᴹᵒᵖ := Functor.mk ⟨mop, .mop⟩

@[simps obj map] -- not necessary but the symmetry with `mopFunctor` looks nicer
def unmopFunctor : Cᴹᵒᵖ ⥤ C := Functor.mk ⟨unmop, .unmop⟩

variable {C}

namespace Iso

abbrev mop {X Y : C} (f : X ≅ Y) : mop X ≅ mop Y := (mopFunctor C).mapIso f

abbrev unmop {X Y : Cᴹᵒᵖ} (f : X ≅ Y) : unmop X ≅ unmop Y := (unmopFunctor C).mapIso f

end Iso

namespace IsIso

instance {X Y : C} (f : X ⟶ Y) [IsIso f] : IsIso f.mop :=
  (mopFunctor C).map_isIso f

instance {X Y : Cᴹᵒᵖ} (f : X ⟶ Y) [IsIso f] : IsIso f.unmop :=
  (unmopFunctor C).map_isIso f

end IsIso

variable [MonoidalCategory.{v₁} C]

open Opposite MonoidalCategory

instance monoidalCategoryOp : MonoidalCategory Cᵒᵖ where
  tensorObj X Y := op (unop X ⊗ unop Y)
  whiskerLeft X _ _ f := (X.unop ◁ f.unop).op
  whiskerRight f X := (f.unop ▷ X.unop).op
  tensorHom f g := (f.unop ⊗ g.unop).op
  tensorHom_def _ _ := Quiver.Hom.unop_inj (tensorHom_def' _ _)
  tensorUnit := op (𝟙_ C)
  associator X Y Z := (α_ (unop X) (unop Y) (unop Z)).symm.op
  leftUnitor X := (λ_ (unop X)).symm.op
  rightUnitor X := (ρ_ (unop X)).symm.op
  associator_naturality f g h := Quiver.Hom.unop_inj <| by simp
  leftUnitor_naturality f := Quiver.Hom.unop_inj <| by simp
  rightUnitor_naturality f := Quiver.Hom.unop_inj <| by simp
  triangle X Y := Quiver.Hom.unop_inj <| by dsimp; monoidal_coherence
  pentagon W X Y Z := Quiver.Hom.unop_inj <| by dsimp; monoidal_coherence

section OppositeLemmas

end OppositeLemmas

instance monoidalCategoryMop : MonoidalCategory Cᴹᵒᵖ where
  tensorObj X Y := mop (unmop Y ⊗ unmop X)
  whiskerLeft X _ _ f := (f.unmop ▷ X.unmop).mop
  whiskerRight f X := (X.unmop ◁ f.unmop).mop
  tensorHom f g := (g.unmop ⊗ f.unmop).mop
  tensorHom_def _ _ := Quiver.Hom.unmop_inj (tensorHom_def' _ _)
  tensorUnit := mop (𝟙_ C)
  associator X Y Z := (α_ (unmop Z) (unmop Y) (unmop X)).symm.mop
  leftUnitor X := (ρ_ (unmop X)).mop
  rightUnitor X := (λ_ (unmop X)).mop
  associator_naturality f g h := Quiver.Hom.unmop_inj <| by simp
  leftUnitor_naturality f := Quiver.Hom.unmop_inj <| by simp
  rightUnitor_naturality f := Quiver.Hom.unmop_inj <| by simp
  -- Porting note: Changed `by coherence` to `by simp` below
  triangle X Y := Quiver.Hom.unmop_inj <| by simp
  pentagon W X Y Z := Quiver.Hom.unmop_inj <| by dsimp; monoidal_coherence

section MonoidalOppositeLemmas

end MonoidalOppositeLemmas

variable (C)

@[simps] def MonoidalOpposite.mopEquiv : C ≌ Cᴹᵒᵖ where
  functor   := mopFunctor C
  inverse   := unmopFunctor C
  unitIso   := Iso.refl _
  counitIso := Iso.refl _

@[simps!] def MonoidalOpposite.unmopEquiv : Cᴹᵒᵖ ≌ C := (mopEquiv C).symm

@[simps!] def MonoidalOpposite.mopMopEquivalence : Cᴹᵒᵖᴹᵒᵖ ≌ C :=
  .trans (MonoidalOpposite.unmopEquiv Cᴹᵒᵖ) (MonoidalOpposite.unmopEquiv C)

@[simps!]
def MonoidalOpposite.tensorIso :
    tensor Cᴹᵒᵖ ≅ (unmopFunctor C).prod (unmopFunctor C) ⋙
      Prod.swap C C ⋙ tensor C ⋙ mopFunctor C :=
  Iso.refl _

variable {C}

@[simps!]
def MonoidalOpposite.tensorLeftIso (X : Cᴹᵒᵖ) :
    tensorLeft X ≅ unmopFunctor C ⋙ tensorRight (unmop X) ⋙ mopFunctor C :=
  Iso.refl _

@[simps!]
def MonoidalOpposite.tensorLeftMopIso (X : C) :
    tensorLeft (mop X) ≅ unmopFunctor C ⋙ tensorRight X ⋙ mopFunctor C :=
  Iso.refl _

@[simps!]
def MonoidalOpposite.tensorLeftUnmopIso (X : Cᴹᵒᵖ) :
    tensorLeft (unmop X) ≅ mopFunctor C ⋙ tensorRight X ⋙ unmopFunctor C :=
  Iso.refl _

@[simps!]
def MonoidalOpposite.tensorRightIso (X : Cᴹᵒᵖ) :
    tensorRight X ≅ unmopFunctor C ⋙ tensorLeft (unmop X) ⋙ mopFunctor C :=
  Iso.refl _

@[simps!]
def MonoidalOpposite.tensorRightMopIso (X : C) :
    tensorRight (mop X) ≅ unmopFunctor C ⋙ tensorLeft X ⋙ mopFunctor C :=
  Iso.refl _

@[simps!]
def MonoidalOpposite.tensorRightUnmopIso (X : Cᴹᵒᵖ) :
    tensorRight (unmop X) ≅ mopFunctor C ⋙ tensorLeft X ⋙ unmopFunctor C :=
  Iso.refl _

end CategoryTheory
