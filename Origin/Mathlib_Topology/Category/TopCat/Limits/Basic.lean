/-
Extracted from Topology/Category/TopCat/Limits/Basic.lean
Genuine: 3 of 4 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# The category of topological spaces has all limits and colimits

Further, these limits and colimits are preserved by the forgetful functor --- that is, the
underlying types are just the limits in the category of types.
-/

open TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite

universe v u u' w

noncomputable section

local notation "forget" => forget TopCat

namespace TopCat

section Limits

variable {J : Type v} [Category.{w} J]

attribute [local fun_prop] continuous_subtype_val

def limitCone (F : J ⥤ TopCat.{max v u}) : Cone F where
  pt := TopCat.of { u : ∀ j : J, F.obj j | ∀ {i j : J} (f : i ⟶ j), F.map f (u i) = u j }
  π :=
    { app := fun j => ofHom
        { toFun := fun u => u.val j
          -- Porting note: `continuity` from the original mathlib3 proof failed here.
          continuous_toFun := Continuous.comp (continuous_apply _) (continuous_subtype_val) }
      naturality := fun X Y f => by
        ext a
        exact (a.2 f).symm }

def limitConeIsLimit (F : J ⥤ TopCat.{max v u}) : IsLimit (limitCone.{v, u} F) where
  lift S := ofHom
    { toFun := fun x =>
        ⟨fun _ => S.π.app _ x, fun f => by
          dsimp
          rw [← S.w f]
          rfl⟩
      continuous_toFun :=
        Continuous.subtype_mk (continuous_pi fun j => (S.π.app j).hom.2) fun x i j f => by
          dsimp
          rw [← S.w f]
          rfl }
  uniq S m h := by
    ext a
    simp [← h]
    rfl

variable {F : J ⥤ TopCat.{u}} (c : Cone (F ⋙ forget))

def conePtOfConeForget : Type _ := c.pt

-- INSTANCE (free from Core): topologicalSpaceConePtOfConeForget
