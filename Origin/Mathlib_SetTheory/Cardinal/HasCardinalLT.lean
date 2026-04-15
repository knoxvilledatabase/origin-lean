/-
Extracted from SetTheory/Cardinal/HasCardinalLT.lean
Genuine: 7 of 7 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The property of being of cardinality less than a cardinal

Given `X : Type u` and `κ : Cardinal.{v}`, we introduce a predicate
`HasCardinalLT X κ` expressing that
`Cardinal.lift.{v} (Cardinal.mk X) < Cardinal.lift κ`.

-/

universe w v u u'

def HasCardinalLT (X : Type u) (κ : Cardinal.{v}) : Prop :=
  Cardinal.lift.{v} (Cardinal.mk X) < Cardinal.lift κ

lemma hasCardinalLT_iff_cardinal_mk_lt (X : Type u) (κ : Cardinal.{u}) :
    HasCardinalLT X κ ↔ Cardinal.mk X < κ := by
  simp [HasCardinalLT]

namespace HasCardinalLT

variable {X : Type u} {κ : Cardinal.{v}} (h : HasCardinalLT X κ)

include h

lemma small : Small.{v} X := by
  dsimp [HasCardinalLT] at h
  rw [← Cardinal.lift_lt.{_, v + 1}, Cardinal.lift_lift, Cardinal.lift_lift] at h
  simpa only [Cardinal.small_iff_lift_mk_lt_univ] using h.trans (Cardinal.lift_lt_univ' κ)

lemma of_le {κ' : Cardinal.{v}} (hκ' : κ ≤ κ') :
    HasCardinalLT X κ' :=
  lt_of_lt_of_le h (by simpa only [Cardinal.lift_le] using hκ')

variable {Y : Type u'}

lemma of_injective (f : Y → X) (hf : Function.Injective f) :
    HasCardinalLT Y κ := by
  dsimp [HasCardinalLT] at h ⊢
  rw [← Cardinal.lift_lt.{_, u}, Cardinal.lift_lift, Cardinal.lift_lift]
  rw [← Cardinal.lift_lt.{_, u'}, Cardinal.lift_lift, Cardinal.lift_lift] at h
  exact lt_of_le_of_lt (Cardinal.mk_le_of_injective
    (Function.Injective.comp ULift.up_injective
      (Function.Injective.comp hf ULift.down_injective))) h

lemma of_surjective (f : X → Y) (hf : Function.Surjective f) :
    HasCardinalLT Y κ := by
  dsimp [HasCardinalLT] at h ⊢
  rw [← Cardinal.lift_lt.{_, u}, Cardinal.lift_lift, Cardinal.lift_lift]
  rw [← Cardinal.lift_lt.{_, u'}, Cardinal.lift_lift, Cardinal.lift_lift] at h
  exact lt_of_le_of_lt (Cardinal.mk_le_of_surjective
    (Function.Surjective.comp ULift.up_surjective (Function.Surjective.comp hf
      ULift.down_surjective))) h

end

end HasCardinalLT

lemma hasCardinalLT_iff_of_equiv {X : Type u} {Y : Type u'} (e : X ≃ Y) (κ : Cardinal.{v}) :
    HasCardinalLT X κ ↔ HasCardinalLT Y κ :=
  ⟨fun h ↦ h.of_injective _ e.symm.injective,
    fun h ↦ h.of_injective _ e.injective⟩
