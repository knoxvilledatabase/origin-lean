/-
Extracted from Algebra/Order/Hom/Normed.lean
Genuine: 8 | Conflates: 0 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core
import Mathlib.Algebra.Order.Hom.Basic
import Mathlib.Analysis.Normed.Group.Basic

noncomputable section

/-!
# Constructing (semi)normed groups from (semi)normed homs

This file defines constructions that upgrade `(Comm)Group` to `(Semi)Normed(Comm)Group`
using a `Group(Semi)normClass` when the codomain is the reals.

See `Mathlib.Algebra.Order.Hom.Ultra` for further upgrades to nonarchimedean normed groups.

-/

variable {F α : Type*} [FunLike F α ℝ]

@[to_additive "Constructs a `SeminormedAddGroup` structure from an `AddGroupSeminormClass` on an

`AddGroup`."]

abbrev GroupSeminormClass.toSeminormedGroup [Group α] [GroupSeminormClass F α ℝ]
    (f : F) : SeminormedGroup α where
  norm := f
  dist x y := f (x / y)
  dist_eq _ _ := rfl
  dist_self _ := by simp
  dist_comm x y := by simp only [← map_inv_eq_map f (x / y), inv_div]
  dist_triangle x y z := by simpa using map_mul_le_add f (x / y) (y / z)

@[to_additive "Constructs a `SeminormedAddCommGroup` structure from an `AddGroupSeminormClass` on an

`AddCommGroup`."]

abbrev GroupSeminormClass.toSeminormedCommGroup [CommGroup α] [GroupSeminormClass F α ℝ]
    (f : F) : SeminormedCommGroup α where
  __ := GroupSeminormClass.toSeminormedGroup f
  __ : CommGroup α := inferInstance

@[to_additive "Constructs a `NormedAddGroup` structure from an `AddGroupNormClass` on an

`AddGroup`."]

abbrev GroupNormClass.toNormedGroup [Group α] [GroupNormClass F α ℝ]
    (f : F) : NormedGroup α where
  __ := GroupSeminormClass.toSeminormedGroup f
  eq_of_dist_eq_zero h := div_eq_one.mp (eq_one_of_map_eq_zero f h)

@[to_additive "Constructs a `NormedAddCommGroup` structure from an `AddGroupNormClass` on an

`AddCommGroup`."]

abbrev GroupNormClass.toNormedCommGroup [CommGroup α] [GroupNormClass F α ℝ]
    (f : F) : NormedCommGroup α where
  __ := GroupNormClass.toNormedGroup f
  __ : CommGroup α := inferInstance
