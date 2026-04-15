/-
Extracted from Algebra/Category/MonCat/Limits.lean
Genuine: 8 of 32 | Dissolved: 0 | Infrastructure: 24
-/
import Origin.Core
import Mathlib.Algebra.Category.MonCat.Basic
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Algebra.Group.Submonoid.Operations
import Mathlib.CategoryTheory.Limits.Creates
import Mathlib.CategoryTheory.Limits.Types
import Mathlib.Logic.Small.Group

/-!
# The category of (commutative) (additive) monoids has all limits

Further, these limits are preserved by the forgetful functor --- that is,
the underlying types are just the limits in the category of types.

-/

noncomputable section

open CategoryTheory

open CategoryTheory.Limits

universe v u w

@[to_additive (attr := nolint checkUnivs) AddMonCatMax
  "An alias for `AddMonCat.{max u v}`, to deal around unification issues."]
abbrev MonCatMax.{u1, u2} := MonCat.{max u1 u2}

namespace MonCat

variable {J : Type v} [Category.{w} J] (F : J ⥤ MonCat.{u})

@[to_additive]
instance monoidObj (j) : Monoid ((F ⋙ forget MonCat).obj j) :=
  inferInstanceAs <| Monoid (F.obj j)

@[to_additive
      "The flat sections of a functor into `AddMonCat` form an additive submonoid of all sections."]
def sectionsSubmonoid : Submonoid (∀ j, F.obj j) where
  carrier := (F ⋙ forget MonCat).sections
  one_mem' {j} {j'} f := by simp
  mul_mem' {a} {b} ah bh {j} {j'} f := by
    simp only [Functor.comp_map, MonoidHom.map_mul, Pi.mul_apply]
    dsimp [Functor.sections] at ah bh
    rw [← ah f, ← bh f, forget_map, map_mul]

@[to_additive]
instance sectionsMonoid : Monoid (F ⋙ forget MonCat.{u}).sections :=
  (sectionsSubmonoid F).toMonoid

variable [Small.{u} (Functor.sections (F ⋙ forget MonCat))]

@[to_additive]
noncomputable instance limitMonoid :
    Monoid (Types.Small.limitCone.{v, u} (F ⋙ forget MonCat.{u})).pt :=
  inferInstanceAs <| Monoid (Shrink (F ⋙ forget MonCat.{u}).sections)

@[to_additive "`limit.π (F ⋙ forget AddMonCat) j` as an `AddMonoidHom`."]
noncomputable def limitπMonoidHom (j : J) :
    (Types.Small.limitCone.{v, u} (F ⋙ forget MonCat.{u})).pt →*
      ((F ⋙ forget MonCat.{u}).obj j) where
  toFun := (Types.Small.limitCone.{v, u} (F ⋙ forget MonCat.{u})).π.app j
  map_one' := by
    simp only [Types.Small.limitCone_pt, Types.Small.limitCone_π_app, equivShrink_symm_one]
    rfl
  map_mul' _ _ := by
    simp only [Types.Small.limitCone_pt, Types.Small.limitCone_π_app, equivShrink_symm_mul]
    rfl

namespace HasLimits

@[to_additive "(Internal use only; use the limits API.)"]
noncomputable def limitCone : Cone F :=
  { pt := MonCat.of (Types.Small.limitCone (F ⋙ forget _)).pt
    π :=
    { app := limitπMonoidHom F
      naturality := fun _ _ f =>
        DFunLike.coe_injective ((Types.Small.limitCone (F ⋙ forget _)).π.naturality f) } }

@[to_additive "(Internal use only; use the limits API.)"]
noncomputable def limitConeIsLimit : IsLimit (limitCone F) := by
  refine IsLimit.ofFaithful (forget MonCat) (Types.Small.limitConeIsLimit.{v,u} _)
    (fun s => { toFun := _, map_one' := ?_, map_mul' := ?_ }) (fun s => rfl)
  · simp only [Functor.mapCone_π_app, forget_map, map_one]
    rfl
  · intro x y
    simp only [Functor.mapCone_π_app, forget_map, map_mul, Functor.comp_obj, Equiv.toFun_as_coe]
    rw [← equivShrink_mul]
    rfl

@[to_additive "If `(F ⋙ forget AddMonCat).sections` is `u`-small, `F` has a limit."]
instance hasLimit : HasLimit F :=
  HasLimit.mk {
    cone := limitCone F
    isLimit := limitConeIsLimit F
  }

@[to_additive "If `J` is `u`-small, `AddMonCat.{u}` has limits of shape `J`."]
instance hasLimitsOfShape [Small.{u} J] : HasLimitsOfShape J MonCat.{u} where
  has_limit _ := inferInstance

end HasLimits

open HasLimits

@[to_additive "The category of additive monoids has all limits.",
  to_additive_relevant_arg 2]
instance hasLimitsOfSize [UnivLE.{v, u}] : HasLimitsOfSize.{w, v} MonCat.{u} where
  has_limits_of_shape _ _ := { }

@[to_additive]
instance hasLimits : HasLimits MonCat.{u} :=
  MonCat.hasLimitsOfSize.{u, u}

@[to_additive "If `J` is `u`-small, the forgetful functor from `AddMonCat.{u}`\n
preserves limits of shape `J`."]
noncomputable instance forget_preservesLimitsOfShape [Small.{u} J] :
    PreservesLimitsOfShape J (forget MonCat.{u}) where
  preservesLimit {F} := preservesLimit_of_preserves_limit_cone (limitConeIsLimit F)
    (Types.Small.limitConeIsLimit (F ⋙ forget _))

@[to_additive
  "The forgetful functor from additive monoids to types preserves all limits.\n\n
  This means the underlying type of a limit can be computed as a limit in the category of types.",
  to_additive_relevant_arg 2]
noncomputable instance forget_preservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget MonCat.{u}) where
  preservesLimitsOfShape := { }

@[to_additive]
noncomputable instance forget_preservesLimits : PreservesLimits (forget MonCat.{u}) :=
  MonCat.forget_preservesLimitsOfSize.{u, u}

end MonCat

open MonCat

@[to_additive (attr := nolint checkUnivs) AddCommMonCatMax
  "An alias for `AddCommMonCat.{max u v}`, to deal around unification issues."]
abbrev CommMonCatMax.{u1, u2} := CommMonCat.{max u1 u2}

namespace CommMonCat

variable {J : Type v} [Category.{w} J] (F : J ⥤ CommMonCat.{u})

@[to_additive]
instance commMonoidObj (j) : CommMonoid ((F ⋙ forget CommMonCat.{u}).obj j) :=
  inferInstanceAs <| CommMonoid (F.obj j)

variable [Small.{u} (Functor.sections (F ⋙ forget CommMonCat))]

@[to_additive]
noncomputable instance limitCommMonoid :
    CommMonoid (Types.Small.limitCone (F ⋙ forget CommMonCat.{u})).pt :=
  letI : CommMonoid (F ⋙ forget CommMonCat.{u}).sections :=
    @Submonoid.toCommMonoid (∀ j, F.obj j) _
      (MonCat.sectionsSubmonoid (F ⋙ forget₂ CommMonCat.{u} MonCat.{u}))
  inferInstanceAs <| CommMonoid (Shrink (F ⋙ forget CommMonCat.{u}).sections)

@[to_additive]
instance : Small.{u} (Functor.sections ((F ⋙ forget₂ CommMonCat MonCat) ⋙ forget MonCat)) :=
  inferInstanceAs <| Small.{u} (Functor.sections (F ⋙ forget CommMonCat))

@[to_additive "We show that the forgetful functor `AddCommMonCat ⥤ AddMonCat` creates limits.\n\n
All we need to do is notice that the limit point has an `AddCommMonoid` instance available,\n
and then reuse the existing limit."]
noncomputable instance forget₂CreatesLimit : CreatesLimit F (forget₂ CommMonCat MonCat.{u}) :=
  createsLimitOfReflectsIso fun c' t =>
    { liftedCone :=
        { pt := CommMonCat.of (Types.Small.limitCone (F ⋙ forget CommMonCat)).pt
          π :=
            { app := MonCat.limitπMonoidHom (F ⋙ forget₂ CommMonCat.{u} MonCat.{u})
              naturality :=
                (MonCat.HasLimits.limitCone
                      (F ⋙ forget₂ CommMonCat MonCat.{u})).π.naturality } }
      validLift := by apply IsLimit.uniqueUpToIso (MonCat.HasLimits.limitConeIsLimit _) t
      makesLimit :=
        IsLimit.ofFaithful (forget₂ CommMonCat MonCat.{u})
          (MonCat.HasLimits.limitConeIsLimit _) (fun _ => _) fun _ => rfl }

@[to_additive "A choice of limit cone for a functor into `AddCommMonCat`.
(Generally, you'll just want to use `limit F`.)"]
noncomputable def limitCone : Cone F :=
  liftLimit (limit.isLimit (F ⋙ forget₂ CommMonCat.{u} MonCat.{u}))

@[to_additive
      "The chosen cone is a limit cone. (Generally, you'll just want to use\n`limit.cone F`.)"]
noncomputable def limitConeIsLimit : IsLimit (limitCone F) :=
  liftedLimitIsLimit _

@[to_additive "If `(F ⋙ forget AddCommMonCat).sections` is `u`-small, `F` has a limit."]
instance hasLimit : HasLimit F :=
  HasLimit.mk {
    cone := limitCone F
    isLimit := limitConeIsLimit F
  }

@[to_additive "If `J` is `u`-small, `AddCommMonCat.{u}` has limits of shape `J`."]
instance hasLimitsOfShape [Small.{u} J] : HasLimitsOfShape J CommMonCat.{u} where
  has_limit _ := inferInstance

@[to_additive "The category of additive commutative monoids has all limits.",
  to_additive_relevant_arg 2]
instance hasLimitsOfSize [UnivLE.{v, u}] : HasLimitsOfSize.{w, v} CommMonCat.{u} where
  has_limits_of_shape _ _ := { }

@[to_additive]
instance hasLimits : HasLimits CommMonCat.{u} :=
  CommMonCat.hasLimitsOfSize.{u, u}

@[to_additive AddCommMonCat.forget₂AddMonPreservesLimitsOfSize "The forgetful functor from
  additive commutative monoids to additive monoids preserves all limits.\n\n
  This means the underlying type of a limit can be computed as a limit in the category of additive\n
  monoids.",
  to_additive_relevant_arg 2]
instance forget₂Mon_preservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget₂ CommMonCat.{u} MonCat.{u}) where
  preservesLimitsOfShape {J} 𝒥 := { }

@[to_additive]
instance forget₂Mon_preservesLimits :
    PreservesLimits (forget₂ CommMonCat.{u} MonCat.{u}) :=
  CommMonCat.forget₂Mon_preservesLimitsOfSize.{u, u}

@[to_additive "If `J` is `u`-small, the forgetful functor from `AddCommMonCat.{u}`\n
preserves limits of shape `J`."]
instance forget_preservesLimitsOfShape [Small.{u} J] :
    PreservesLimitsOfShape J (forget CommMonCat.{u}) where
  preservesLimit {F} := preservesLimit_of_preserves_limit_cone (limitConeIsLimit F)
    (Types.Small.limitConeIsLimit (F ⋙ forget _))

@[to_additive "The forgetful functor from additive commutative monoids to types preserves all\n
limits.\n\n
This means the underlying type of a limit can be computed as a limit in the category of types."]
instance forget_preservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{v, v} (forget CommMonCat.{u}) where
  preservesLimitsOfShape {_} _ := { }

instance _root_.AddCommMonCat.forget_preservesLimits :
    PreservesLimits (forget AddCommMonCat.{u}) :=
  AddCommMonCat.forget_preservesLimitsOfSize.{u, u}

@[to_additive existing]
instance forget_preservesLimits : PreservesLimits (forget CommMonCat.{u}) :=
  CommMonCat.forget_preservesLimitsOfSize.{u, u}

end CommMonCat
