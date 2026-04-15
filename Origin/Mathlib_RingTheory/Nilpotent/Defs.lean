/-
Extracted from RingTheory/Nilpotent/Defs.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Definition of nilpotent elements

This file proves basic facts about nilpotent elements.
For results that require further theory, see `Mathlib/RingTheory/Nilpotent/Basic.lean`
and `Mathlib/RingTheory/Nilpotent/Lemmas.lean`.

## Main definitions

  * `Commute.isNilpotent_mul_left`
  * `Commute.isNilpotent_mul_right`
  * `nilpotencyClass`

-/

open Set

variable {R S : Type*} {x y : R}

theorem IsNilpotent.map [MonoidWithZero R] [MonoidWithZero S] {r : R} {F : Type*}
    [FunLike F R S] [MonoidWithZeroHomClass F R S] (hr : IsNilpotent r) (f : F) :
    IsNilpotent (f r) := by
  use hr.choose
  rw [← map_pow, hr.choose_spec, map_zero]

lemma IsNilpotent.map_iff [MonoidWithZero R] [MonoidWithZero S] {r : R} {F : Type*}
    [FunLike F R S] [MonoidWithZeroHomClass F R S] {f : F} (hf : Function.Injective f) :
    IsNilpotent (f r) ↔ IsNilpotent r :=
  ⟨fun ⟨k, hk⟩ ↦ ⟨k, (map_eq_zero_iff f hf).mp <| by rwa [map_pow]⟩, fun h ↦ h.map f⟩

theorem IsUnit.isNilpotent_mul_unit_of_commute_iff [MonoidWithZero R] {r u : R}
    (hu : IsUnit u) (h_comm : Commute r u) :
    IsNilpotent (r * u) ↔ IsNilpotent r :=
  exists_congr fun n ↦ by rw [h_comm.mul_pow, (hu.pow n).mul_left_eq_zero]

theorem IsUnit.isNilpotent_unit_mul_of_commute_iff [MonoidWithZero R] {r u : R}
    (hu : IsUnit u) (h_comm : Commute r u) :
    IsNilpotent (u * r) ↔ IsNilpotent r :=
  h_comm ▸ hu.isNilpotent_mul_unit_of_commute_iff h_comm

section NilpotencyClass

section ZeroPow

variable [Zero R] [Pow R ℕ]

variable (x) in

noncomputable def nilpotencyClass : ℕ := sInf {k | x ^ k = 0}
