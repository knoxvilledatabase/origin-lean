/-
Extracted from RingTheory/DedekindDomain/Different.lean
Genuine: 7 of 7 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The different ideal

## Main definition
- `Submodule.traceDual`: The dual `L`-sub `B`-module under the trace form.
- `FractionalIdeal.dual`: The dual fractional ideal under the trace form.
- `differentIdeal`: The different ideal of an extension of integral domains.

## Main results
- `conductor_mul_differentIdeal`:
  If `L = K[x]`, with `x` integral over `A`, then `𝔣 * 𝔇 = (f'(x))`
    with `f` being the minimal polynomial of `x`.
- `aeval_derivative_mem_differentIdeal`:
  If `L = K[x]`, with `x` integral over `A`, then `f'(x) ∈ 𝔇`
    with `f` being the minimal polynomial of `x`.
- `not_dvd_differentIdeal_iff`: A prime does not divide the different ideal iff it is unramified
  (in the sense of `Algebra.IsUnramifiedAt`).
- `differentIdeal_eq_differentIdeal_mul_differentIdeal`: Transitivity of the different ideal.

## TODO
- Show properties of the different ideal
-/

open Module

universe u

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

  Ideal.Quotient.field

variable (A K : Type*) {L : Type u} {B} [CommRing A] [Field K] [CommRing B] [Field L]

variable [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]

variable [IsScalarTower A K L] [IsScalarTower A B L]

open nonZeroDivisors IsLocalization Matrix Algebra Pointwise Polynomial Submodule

section BIsDomain

noncomputable

def Submodule.traceDual (I : Submodule B L) : Submodule B L where
  __ := (traceForm K L).dualSubmodule (I.restrictScalars A)
  smul_mem' c x hx a ha := by
    rw [traceForm_apply, smul_mul_assoc, mul_comm, ← smul_mul_assoc, mul_comm]
    exact hx _ (Submodule.smul_mem _ c ha)

variable {A K}

local notation:max I:max "ᵛ" => Submodule.traceDual A K I

namespace Submodule

lemma mem_traceDual {I : Submodule B L} {x} :
    x ∈ Iᵛ ↔ ∀ a ∈ I, traceForm K L x a ∈ (algebraMap A K).range :=
  forall₂_congr fun _ _ ↦ mem_one

lemma le_traceDual_iff_map_le_one {I J : Submodule B L} :
    I ≤ Jᵛ ↔ ((I * J : Submodule B L).restrictScalars A).map
      ((trace K L).restrictScalars A) ≤ 1 := by
  rw [Submodule.map_le_iff_le_comap, Submodule.restrictScalars_mul, Submodule.mul_le]
  simp [SetLike.le_def, mem_traceDual]

lemma le_traceDual_mul_iff {I J J' : Submodule B L} :
    I ≤ (J * J')ᵛ ↔ I * J ≤ J'ᵛ := by
  simp_rw [le_traceDual_iff_map_le_one, mul_assoc]

lemma le_traceDual {I J : Submodule B L} :
    I ≤ Jᵛ ↔ I * J ≤ 1ᵛ := by
  rw [← le_traceDual_mul_iff, mul_one]

lemma le_traceDual_comm {I J : Submodule B L} :
    I ≤ Jᵛ ↔ J ≤ Iᵛ := by rw [le_traceDual, mul_comm, ← le_traceDual]

lemma le_traceDual_traceDual {I : Submodule B L} :
    I ≤ Iᵛᵛ := le_traceDual_comm.mpr le_rfl
