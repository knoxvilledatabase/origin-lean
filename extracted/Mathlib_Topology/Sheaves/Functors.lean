/-
Extracted from Topology/Sheaves/Functors.lean
Genuine: 6 | Conflates: 0 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Mathlib.CategoryTheory.Sites.Pullback

noncomputable section

/-!
# functors between categories of sheaves

Show that the pushforward of a sheaf is a sheaf, and define
the pushforward functor from the category of C-valued sheaves
on X to that of sheaves on Y, given a continuous map between
topological spaces X and Y.

## Main definitions
- `TopCat.Sheaf.pushforward`:
    The pushforward functor between sheaf categories over topological spaces.
- `TopCat.Sheaf.pullback`: The pullback functor between sheaf categories over topological spaces.
- `TopCat.Sheaf.pullbackPushforwardAdjunction`:
  The adjunction between pullback and pushforward for sheaves on topological spaces.

-/

noncomputable section

universe w v u

open CategoryTheory

open CategoryTheory.Limits

open TopologicalSpace

open scoped AlgebraicGeometry

variable {C : Type u} [Category.{v} C]

variable {X Y : TopCat.{w}} (f : X ⟶ Y)

variable ⦃ι : Type w⦄ {U : ι → Opens Y}

namespace TopCat

namespace Sheaf

open Presheaf

theorem pushforward_sheaf_of_sheaf {F : X.Presheaf C} (h : F.IsSheaf) : (f _* F).IsSheaf :=
  (Opens.map f).op_comp_isSheaf _ _ ⟨_, h⟩

variable (C)

def pushforward (f : X ⟶ Y) : X.Sheaf C ⥤ Y.Sheaf C :=
  (Opens.map f).sheafPushforwardContinuous _ _ _

def pushforwardForgetIso (f : X ⟶ Y) :
    pushforward C f ⋙ forget C Y ≅ forget C X ⋙ Presheaf.pushforward C f := Iso.refl _

variable {C}

@[simp] lemma pushforward_obj_val (f : X ⟶ Y) (F : X.Sheaf C) :
    ((pushforward C f).obj F).1 = f _* F.1 := rfl

@[simp] lemma pushforward_map (f : X ⟶ Y) {F F' : X.Sheaf C} (α : F ⟶ F') :
    ((pushforward C f).map α).1 = (Presheaf.pushforward C f).map α.1 := rfl

variable (A : Type*) [Category.{w} A] [ConcreteCategory.{w} A] [HasColimits A] [HasLimits A]

variable [PreservesLimits (CategoryTheory.forget A)]

variable [PreservesFilteredColimits (CategoryTheory.forget A)]

variable [(CategoryTheory.forget A).ReflectsIsomorphisms]

def pullback (f : X ⟶ Y) : Y.Sheaf A ⥤ X.Sheaf A :=
  (Opens.map f).sheafPullback _ _ _

def pullbackIso (f : X ⟶ Y) :
    pullback A f ≅ forget A Y ⋙ Presheaf.pullback A f ⋙ presheafToSheaf _ _ := Iso.refl _

def pullbackPushforwardAdjunction (f : X ⟶ Y) :
    pullback A f ⊣ pushforward A f :=
  (Opens.map f).sheafAdjunctionContinuous _ _ _

instance : (pullback A f).IsLeftAdjoint  := (pullbackPushforwardAdjunction A f).isLeftAdjoint

instance : (pushforward A f).IsRightAdjoint := (pullbackPushforwardAdjunction A f).isRightAdjoint

end Sheaf

end TopCat
