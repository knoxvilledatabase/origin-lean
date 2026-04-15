/-
Extracted from NumberTheory/NumberField/Completion/FinitePlace.lean
Genuine: 8 of 21 | Dissolved: 4 | Infrastructure: 9
-/
import Origin.Core

/-!
# Finite places of number fields
This file defines finite places of a number field `K` as absolute values coming from an embedding
into a completion of `K` associated to a non-zero prime ideal of `𝓞 K`.

Many of the results in this file are expressed in the generality of: `R` is a Dedekind domain
with field of fractions `K` such that `Module.Finite ℤ R` and `Module.Free ℤ R`. If `K` is
a number field, then this characterises `R` as being isomorphic to `𝓞 K` without explicitly
requiring `𝓞 K`. This is so that `ℤ` and `𝓞 ℚ` can be used interchangeably.

## Main Definitions and Results
* `NumberField.adicAbv`: a `v`-adic absolute value on `K`.
* `NumberField.FinitePlace`: the type of finite places of a number field `K`.
* `NumberField.FinitePlace.embedding`: the canonical embedding of a number field `K` to the
  `v`-adic completion `v.adicCompletion K` of `K`, where `v` is a non-zero prime ideal of `𝓞 K`
* `NumberField.FinitePlace.norm_embedding`: the norm of `embedding v x` is the same as the `v`-adic
  absolute value of `x`. See also `NumberField.FinitePlace.norm_embedding'` and
  `NumberField.FinitePlace.norm_embedding_int` for versions where the `v`-adic absolute value is
  unfolded.
* `NumberField.FinitePlace.hasFiniteMulSupport`: the `v`-adic absolute value of a non-zero element
  of `K` is different from 1 for at most finitely many `v`.
*  The valuation subrings of the field at the `v`-valuation and it's adic completion are
   discrete valuation rings.

## Tags
number field, places, finite places
-/

open Ideal IsDedekindDomain HeightOneSpectrum WithZeroMulInt WithZero

open scoped WithZero NNReal

section DVR

variable (A : Type*) [CommRing A] [IsDedekindDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (v : HeightOneSpectrum A) (hv : Finite (A ⧸ v.asIdeal))

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

end DVR

namespace NumberField

variable {K : Type*} [Field K] {R : Type*} [CommRing R] [Algebra R K] [IsDedekindDomain R]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

noncomputable def FinitePlace.embedding : K →+* adicCompletion K v :=
  UniformSpace.Completion.coeRingHom.comp (WithVal.equiv (v.valuation K)).symm

section AbsoluteValue

-- INSTANCE (free from Core): :

section FiniteFree

/-! In this section we assume further that `Module.Finite ℤ R` and `Module.Free ℤ R`.
This characterises `R` as being isomorphic to `𝓞 K` without explicitly requiring that type.
As a result, if `F = ℚ`, then we can use `ℤ` and `𝓞 ℚ` interchangeably. -/

variable [Module.Finite ℤ R] [Module.Free ℤ R]

namespace HeightOneSpectrum

lemma one_lt_absNorm : 1 < absNorm v.asIdeal := by
  by_contra! h
  apply IsPrime.ne_top v.isPrime
  rw [← absNorm_eq_one_iff]
  have : 0 < absNorm v.asIdeal := by
    rw [Nat.pos_iff_ne_zero, absNorm_ne_zero_iff]
    exact v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  lia

lemma one_lt_absNorm_nnreal : 1 < (absNorm v.asIdeal : ℝ≥0) := mod_cast one_lt_absNorm v

-- DISSOLVED: absNorm_ne_zero

variable (K)

noncomputable def adicAbv : AbsoluteValue K ℝ := v.adicAbv <| one_lt_absNorm_nnreal v

-- DISSOLVED: adicAbv_def

theorem isNonarchimedean_adicAbv : IsNonarchimedean (adicAbv K v) :=
  v.isNonarchimedean_adicAbv <| one_lt_absNorm_nnreal v

open Valuation.IsRankOneDiscrete

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): instRankOneAdicCompletion

-- DISSOLVED: rankOne_hom'_def

-- INSTANCE (free from Core): instNormedFieldValuedAdicCompletion

-- DISSOLVED: toNNReal_valued_eq_adicAbv

theorem adicAbv_add_le_max (x y : K) :
    adicAbv K v (x + y) ≤ (adicAbv K v x) ⊔ (adicAbv K v y) := isNonarchimedean_adicAbv K v x y

theorem adicAbv_natCast_le_one (n : ℕ) : adicAbv K v n ≤ 1 :=
  (isNonarchimedean_adicAbv K v).apply_natCast_le_one_of_isNonarchimedean

theorem adicAbv_intCast_le_one (n : ℤ) : adicAbv K v n ≤ 1 :=
  (isNonarchimedean_adicAbv K v).apply_intCast_le_one_of_isNonarchimedean
