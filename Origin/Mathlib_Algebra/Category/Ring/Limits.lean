/-
Extracted from Algebra/Category/Ring/Limits.lean
Genuine: 15 of 65 | Dissolved: 0 | Infrastructure: 50
-/
import Origin.Core

/-!
# The category of (commutative) rings has all limits

Further, these limits are preserved by the forgetful functor --- that is,
the underlying types are just the limits in the category of types.
-/

library_note «change elaboration strategy with `by apply`» /--

Some definitions may be extremely slow to elaborate, when the target type to be constructed

is complicated and when the type of the term given in the definition is also complicated and does

not obviously match the target type. In this case, instead of just giving the term, prefixing it

with `by apply` may speed up things considerably as the types are not elaborated in the same order.

-/

open CategoryTheory

open CategoryTheory.Limits

universe v u w

noncomputable section

namespace SemiRingCat

variable {J : Type v} [Category.{w} J] (F : J ⥤ SemiRingCat.{u})

-- INSTANCE (free from Core): semiringObj

def sectionsSubsemiring : Subsemiring (∀ j, F.obj j) :=
  { (MonCat.sectionsSubmonoid (J := J) (F ⋙ forget₂ SemiRingCat.{u} MonCat.{u})),
    (AddMonCat.sectionsAddSubmonoid (J := J) (F ⋙ forget₂ SemiRingCat.{u} AddCommMonCat.{u} ⋙
      forget₂ AddCommMonCat AddMonCat)) with
    carrier := (F ⋙ forget SemiRingCat).sections }

-- INSTANCE (free from Core): sectionsSemiring

variable [Small.{u} (Functor.sections (F ⋙ forget SemiRingCat.{u}))]

-- INSTANCE (free from Core): limitSemiring

def limitπRingHom (j) :
    (Types.Small.limitCone.{v, u} (F ⋙ forget SemiRingCat)).pt →+* (F ⋙ forget SemiRingCat).obj j :=
  let f : J ⥤ AddMonCat.{u} := F ⋙ forget₂ SemiRingCat.{u} AddCommMonCat.{u} ⋙
    forget₂ AddCommMonCat AddMonCat
  let _ : Small.{u} (Functor.sections ((F ⋙ forget₂ _ MonCat) ⋙ forget MonCat)) :=
    inferInstanceAs <| Small.{u} (Functor.sections (F ⋙ forget SemiRingCat.{u}))
  let _ : Small.{u} (Functor.sections (f ⋙ forget AddMonCat)) :=
    inferInstanceAs <| Small.{u} (Functor.sections (F ⋙ forget SemiRingCat.{u}))
  { AddMonCat.limitπAddMonoidHom f j,
    MonCat.limitπMonoidHom (F ⋙ forget₂ SemiRingCat MonCat.{u}) j with
    toFun := (Types.Small.limitCone (F ⋙ forget SemiRingCat)).π.app j }

namespace HasLimits

def limitCone : Cone F where
  pt := SemiRingCat.of (Types.Small.limitCone (F ⋙ forget _)).pt
  π :=
    { app := fun j ↦ SemiRingCat.ofHom <| limitπRingHom.{v, u} F j
      naturality _ _ f := by
        ext
        simpa using (Types.Small.limitCone (F ⋙ forget _)).π.naturality_apply f _ }

set_option backward.isDefEq.respectTransparency false in

def limitConeIsLimit : IsLimit (limitCone F) := by
  refine IsLimit.ofFaithful (forget SemiRingCat.{u}) (Types.Small.limitConeIsLimit.{v, u} _)
    (fun s => ofHom { toFun := _, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ })
    (fun s => rfl)
  · simp
    rfl
  · intro x y
    simp [← equivShrink_mul]
    rfl
  · simp
    rfl
  · intro x y
    simp [← equivShrink_add]
    rfl

end HasLimits

open HasLimits

-- INSTANCE (free from Core): hasLimit

-- INSTANCE (free from Core): hasLimitsOfShape

-- INSTANCE (free from Core): hasLimitsOfSize

-- INSTANCE (free from Core): hasLimits

def forget₂AddCommMonPreservesLimitsAux :
    IsLimit ((forget₂ SemiRingCat AddCommMonCat).mapCone (limitCone F)) := by
  let _ : Small.{u} (Functor.sections ((F ⋙ forget₂ _ AddCommMonCat) ⋙ forget _)) :=
    inferInstanceAs <| Small.{u} (Functor.sections (F ⋙ forget SemiRingCat))
  apply AddCommMonCat.limitConeIsLimit.{v, u}

-- INSTANCE (free from Core): forget₂AddCommMon_preservesLimitsOfSize

-- INSTANCE (free from Core): forget₂AddCommMon_preservesLimits

def forget₂MonPreservesLimitsAux :
    IsLimit ((forget₂ SemiRingCat MonCat).mapCone (limitCone F)) := by
  let _ : Small.{u} (Functor.sections ((F ⋙ forget₂ _ MonCat) ⋙ forget MonCat)) :=
    inferInstanceAs <| Small.{u} (Functor.sections (F ⋙ forget SemiRingCat))
  apply MonCat.HasLimits.limitConeIsLimit (F ⋙ forget₂ SemiRingCat MonCat.{u})

-- INSTANCE (free from Core): forget₂Mon_preservesLimitsOfSize

-- INSTANCE (free from Core): forget₂Mon_preservesLimits

-- INSTANCE (free from Core): forget_preservesLimitsOfSize

-- INSTANCE (free from Core): forget_preservesLimits

end SemiRingCat

namespace CommSemiRingCat

variable {J : Type v} [Category.{w} J] (F : J ⥤ CommSemiRingCat.{u})

-- INSTANCE (free from Core): commSemiringObj

variable [Small.{u} (Functor.sections (F ⋙ forget CommSemiRingCat))]

-- INSTANCE (free from Core): limitCommSemiring

-- INSTANCE (free from Core): :

def limitCone : Cone F :=
  let _ : Small.{u} (Functor.sections ((F ⋙ forget₂ _ SemiRingCat.{u}) ⋙ forget _)) :=
    inferInstanceAs <| Small.{u} (Functor.sections (F ⋙ forget _))
  liftLimit (limit.isLimit (F ⋙ forget₂ CommSemiRingCat.{u} SemiRingCat.{u}))

def limitConeIsLimit : IsLimit (limitCone F) :=
  liftedLimitIsLimit _

-- INSTANCE (free from Core): hasLimit

-- INSTANCE (free from Core): hasLimitsOfShape

-- INSTANCE (free from Core): hasLimitsOfSize

-- INSTANCE (free from Core): hasLimits

-- INSTANCE (free from Core): forget₂SemiRing_preservesLimitsOfSize

-- INSTANCE (free from Core): forget₂SemiRing_preservesLimits

-- INSTANCE (free from Core): forget_preservesLimitsOfSize

-- INSTANCE (free from Core): forget_preservesLimits

end CommSemiRingCat

namespace RingCat

variable {J : Type v} [Category.{w} J] (F : J ⥤ RingCat.{u})

-- INSTANCE (free from Core): ringObj

def sectionsSubring : Subring (∀ j, F.obj j) :=
  let f : J ⥤ AddGrpCat.{u} :=
    F ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u} ⋙
    forget₂ AddCommGrpCat.{u} AddGrpCat.{u}
  let g : J ⥤ SemiRingCat.{u} := F ⋙ forget₂ RingCat.{u} SemiRingCat.{u}
  { AddGrpCat.sectionsAddSubgroup (J := J) f,
    SemiRingCat.sectionsSubsemiring (J := J) g with
    carrier := (F ⋙ forget RingCat.{u}).sections }

variable [Small.{u} (Functor.sections (F ⋙ forget RingCat.{u}))]

-- INSTANCE (free from Core): limitRing

-- INSTANCE (free from Core): :

def limitCone : Cone F :=
  let _ : Small.{u} (Functor.sections ((F ⋙ forget₂ _ SemiRingCat) ⋙ forget _)) :=
    inferInstanceAs <| Small.{u} (Functor.sections (F ⋙ forget _))
  liftLimit (limit.isLimit (F ⋙ forget₂ RingCat.{u} SemiRingCat.{u}))

def limitConeIsLimit : IsLimit (limitCone F) :=
  liftedLimitIsLimit _

-- INSTANCE (free from Core): hasLimit

-- INSTANCE (free from Core): hasLimitsOfShape

-- INSTANCE (free from Core): hasLimitsOfSize

-- INSTANCE (free from Core): hasLimits

-- INSTANCE (free from Core): forget₂SemiRing_preservesLimitsOfSize

-- INSTANCE (free from Core): forget₂SemiRing_preservesLimits

def forget₂AddCommGroupPreservesLimitsAux :
    IsLimit ((forget₂ RingCat.{u} AddCommGrpCat).mapCone (limitCone.{v, u} F)) := by
  let _ : Small.{u} (Functor.sections ((F ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u}) ⋙ forget _)) :=
    inferInstanceAs <| Small.{u} (Functor.sections (F ⋙ forget _))
  apply AddCommGrpCat.limitConeIsLimit.{v, u} _

-- INSTANCE (free from Core): forget₂AddCommGroup_preservesLimitsOfSize

-- INSTANCE (free from Core): forget₂AddCommGroup_preservesLimits

-- INSTANCE (free from Core): forget_preservesLimitsOfSize

-- INSTANCE (free from Core): forget_preservesLimits

end RingCat

namespace CommRingCat

variable {J : Type v} [Category.{w} J] (F : J ⥤ CommRingCat.{u})

-- INSTANCE (free from Core): commRingObj

variable [Small.{u} (Functor.sections (F ⋙ forget CommRingCat))]

-- INSTANCE (free from Core): limitCommRing

#adaptation_note /-- After nightly-2026-02-23 we need this to avoid timeouts. -/

-- INSTANCE (free from Core): :

def limitCone : Cone F :=
  let _ : Small.{u} (Functor.sections ((F ⋙ forget₂ CommRingCat RingCat) ⋙ forget RingCat)) :=
    inferInstanceAs <| Small.{u} (Functor.sections (F ⋙ forget _))
  liftLimit (limit.isLimit (F ⋙ forget₂ CommRingCat.{u} RingCat.{u}))

def limitConeIsLimit : IsLimit (limitCone.{v, u} F) :=
  liftedLimitIsLimit _

-- INSTANCE (free from Core): hasLimit

-- INSTANCE (free from Core): hasLimitsOfShape

-- INSTANCE (free from Core): hasLimitsOfSize

-- INSTANCE (free from Core): hasLimits

-- INSTANCE (free from Core): forget₂Ring_preservesLimitsOfSize

-- INSTANCE (free from Core): forget₂Ring_preservesLimits

#adaptation_note /-- After nightly-2026-02-23 this requires more heartbeats. -/

set_option maxHeartbeats 400000 in -- see note above

def forget₂CommSemiRingPreservesLimitsAux :
    IsLimit ((forget₂ CommRingCat CommSemiRingCat).mapCone (limitCone F)) := by
  let _ : Small.{u} ((F ⋙ forget₂ _ CommSemiRingCat) ⋙ forget _).sections :=
    inferInstanceAs <| Small.{u} (F ⋙ forget _).sections
  apply CommSemiRingCat.limitConeIsLimit (F ⋙ forget₂ CommRingCat CommSemiRingCat.{u})

-- INSTANCE (free from Core): forget₂CommSemiRing_preservesLimitsOfSize

-- INSTANCE (free from Core): forget₂CommSemiRing_preservesLimits

-- INSTANCE (free from Core): forget_preservesLimitsOfSize

-- INSTANCE (free from Core): forget_preservesLimits

end CommRingCat
