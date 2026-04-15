/-
Extracted from Algebra/Category/ModuleCat/Limits.lean
Genuine: 7 of 26 | Dissolved: 0 | Infrastructure: 19
-/
import Origin.Core

/-!
# The category of R-modules has all limits

Further, these limits are preserved by the forgetful functor --- that is,
the underlying types are just the limits in the category of types.
-/

open CategoryTheory

open CategoryTheory.Limits

universe t v w u

noncomputable section

namespace ModuleCat

variable {R : Type u} [Ring R]

variable {J : Type v} [Category.{t} J] (F : J ⥤ ModuleCat.{w} R)

-- INSTANCE (free from Core): addCommGroupObj

-- INSTANCE (free from Core): moduleObj

set_option backward.isDefEq.respectTransparency false in

def sectionsSubmodule : Submodule R (∀ j, F.obj j) :=
  { AddGrpCat.sectionsAddSubgroup.{v, w}
      (F ⋙ forget₂ (ModuleCat R) AddCommGrpCat.{w} ⋙
          forget₂ AddCommGrpCat AddGrpCat.{w}) with
    carrier := (F ⋙ forget (ModuleCat R)).sections
    smul_mem' := fun r s sh j j' f => by
      simpa [Functor.sections] using congr_arg (r • ·) (sh f) }

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

variable [Small.{w} (Functor.sections (F ⋙ forget (ModuleCat R)))]

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): limitAddCommMonoid

-- INSTANCE (free from Core): limitAddCommGroup

-- INSTANCE (free from Core): limitModule

set_option backward.isDefEq.respectTransparency false in

def limitπLinearMap (j) :
    (Types.Small.limitCone (F ⋙ forget (ModuleCat.{w} R))).pt →ₗ[R]
      (F ⋙ forget (ModuleCat R)).obj j where
  toFun := (Types.Small.limitCone (F ⋙ forget (ModuleCat R))).π.app j
  map_smul' _ _ := by simp; rfl
  map_add' _ _ := by simp; rfl

namespace HasLimits

def limitCone : Cone F where
  pt := ModuleCat.of R (Types.Small.limitCone.{v, w} (F ⋙ forget _)).pt
  π :=
    { app j := ofHom (limitπLinearMap F j)
      naturality _ _ f := by
        ext
        simpa using (Types.Small.limitCone (F ⋙ forget _)).π.naturality_apply f _ }

set_option backward.isDefEq.respectTransparency false in

def limitConeIsLimit : IsLimit (limitCone.{t, v, w} F) := by
  refine IsLimit.ofFaithful (forget (ModuleCat R)) (Types.Small.limitConeIsLimit.{v, w} _)
    (fun s => ofHom ⟨⟨(Types.Small.limitConeIsLimit.{v, w} _).lift
                ((forget (ModuleCat R)).mapCone s), ?_⟩, ?_⟩)
    (fun s => rfl)
  · intro x y
    simp [← equivShrink_add]
    rfl
  · intro r x
    simp [← equivShrink_smul]
    rfl

end HasLimits

open HasLimits

-- INSTANCE (free from Core): hasLimit

lemma hasLimitsOfShape [Small.{w} J] : HasLimitsOfShape J (ModuleCat.{w} R) where

lemma hasLimitsOfSize [UnivLE.{v, w}] : HasLimitsOfSize.{t, v} (ModuleCat.{w} R) where
  has_limits_of_shape _ := hasLimitsOfShape

-- INSTANCE (free from Core): hasLimits

-- INSTANCE (free from Core): (priority

def forget₂AddCommGroup_preservesLimitsAux :
    IsLimit ((forget₂ (ModuleCat R) AddCommGrpCat).mapCone (limitCone F)) :=
  letI : Small.{w} (Functor.sections ((F ⋙ forget₂ _ AddCommGrpCat) ⋙ forget _)) :=
    inferInstanceAs <| Small.{w} (Functor.sections (F ⋙ forget (ModuleCat R)))
  AddCommGrpCat.limitConeIsLimit
    (F ⋙ forget₂ (ModuleCat.{w} R) _ : J ⥤ AddCommGrpCat.{w})

-- INSTANCE (free from Core): forget₂AddCommGroup_preservesLimit

-- INSTANCE (free from Core): forget₂AddCommGroup_preservesLimitsOfSize

-- INSTANCE (free from Core): forget₂AddCommGroup_preservesLimits

-- INSTANCE (free from Core): forget_preservesLimitsOfSize

-- INSTANCE (free from Core): forget_preservesLimits

end

-- INSTANCE (free from Core): forget₂AddCommGroup_reflectsLimit

-- INSTANCE (free from Core): forget₂AddCommGroup_reflectsLimitOfShape

-- INSTANCE (free from Core): forget₂AddCommGroup_reflectsLimitOfSize

section DirectLimit

open Module

variable {ι : Type v}

variable [DecidableEq ι] [Preorder ι]

variable (G : ι → Type v)

variable [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]

variable (f : ∀ i j, i ≤ j → G i →ₗ[R] G j) [DirectedSystem G fun i j h ↦ f i j h]
