/-
Extracted from Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow.lean
Genuine: 52 | Conflates: 0 | Dissolved: 0 | Infrastructure: 11
-/
import Origin.Core
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

noncomputable section

/-!
# Real powers defined via the continuous functional calculus

This file defines real powers via the continuous functional calculus (CFC) and builds its API.
This allows one to take real powers of matrices, operators, elements of a C⋆-algebra, etc. The
square root is also defined via the non-unital CFC.

## Main declarations

+ `CFC.nnrpow`: the `ℝ≥0` power function based on the non-unital CFC, i.e. `cfcₙ NNReal.rpow`
  composed with `(↑) : ℝ≥0 → ℝ`.
+ `CFC.sqrt`: the square root function based on the non-unital CFC, i.e. `cfcₙ NNReal.sqrt`
+ `CFC.rpow`: the real power function based on the unital CFC, i.e. `cfc NNReal.rpow`

## Implementation notes

We define two separate versions `CFC.nnrpow` and `CFC.rpow` due to what happens at 0. Since
`NNReal.rpow 0 0 = 1`, this means that this function does not map zero to zero when the exponent
is zero, and hence `CFC.nnrpow a 0 = 0` whereas `CFC.rpow a 0 = 1`. Note that the non-unital version
only makes sense for nonnegative exponents, and hence we define it such that the exponent is in
`ℝ≥0`.

## Notation

+ We define a `Pow A ℝ` instance for `CFC.rpow`, i.e `a ^ y` with `A` an operator and `y : ℝ` works
  as expected. Likewise, we define a `Pow A ℝ≥0` instance for `CFC.nnrpow`. Note that these are
  low-priority instances, in order to avoid overriding instances such as `Pow ℝ ℝ`.

## TODO

+ Relate these to the log and exp functions
+ Lemmas about how these functions interact with commuting `a` and `b`.
+ Prove the order properties (operator monotonicity and concavity/convexity)
-/

open scoped NNReal

namespace NNReal

noncomputable abbrev nnrpow (a : ℝ≥0) (b : ℝ≥0) : ℝ≥0 := a ^ (b : ℝ)

@[simp] lemma nnrpow_def (a b : ℝ≥0) : nnrpow a b = a ^ (b : ℝ) := rfl

@[fun_prop]
lemma continuous_nnrpow_const (y : ℝ≥0) : Continuous (nnrpow · y) :=
  continuous_rpow_const zero_le_coe

attribute [fun_prop] continuousOn_rpow_const

end NNReal

namespace CFC

section NonUnital

variable {A : Type*} [PartialOrder A] [NonUnitalNormedRing A] [StarRing A]
  [Module ℝ≥0 A] [SMulCommClass ℝ≥0 A A] [IsScalarTower ℝ≥0 A A]
  [NonUnitalContinuousFunctionalCalculus ℝ≥0 (fun (a : A) => 0 ≤ a)]

noncomputable def nnrpow (a : A) (y : ℝ≥0) : A := cfcₙ (NNReal.nnrpow · y) a

noncomputable instance (priority := 100) : Pow A ℝ≥0 where
  pow a y := nnrpow a y

@[simp]
lemma nnrpow_eq_pow {a : A} {y : ℝ≥0} : nnrpow a y = a ^ y := rfl

@[simp]
lemma nnrpow_nonneg {a : A} {x : ℝ≥0} : 0 ≤ a ^ x := cfcₙ_predicate _ a

lemma nnrpow_def {a : A} {y : ℝ≥0} : a ^ y = cfcₙ (NNReal.nnrpow · y) a := rfl

lemma nnrpow_add {a : A} {x y : ℝ≥0} (hx : 0 < x) (hy : 0 < y) :
    a ^ (x + y) = a ^ x * a ^ y := by
  simp only [nnrpow_def]
  rw [← cfcₙ_mul _ _ a]
  congr! 2 with z
  exact mod_cast z.rpow_add' <| ne_of_gt (add_pos hx hy)

@[simp]
lemma nnrpow_zero {a : A} : a ^ (0 : ℝ≥0) = 0 := by
  simp [nnrpow_def, cfcₙ_apply_of_not_map_zero]

lemma nnrpow_one (a : A) (ha : 0 ≤ a := by cfc_tac) : a ^ (1 : ℝ≥0) = a := by
  simp only [nnrpow_def, NNReal.nnrpow_def, NNReal.coe_one, NNReal.rpow_one]
  change cfcₙ (id : ℝ≥0 → ℝ≥0) a = a
  rw [cfcₙ_id ℝ≥0 a]

lemma nnrpow_two (a : A) (ha : 0 ≤ a := by cfc_tac) : a ^ (2 : ℝ≥0) = a * a := by
  simp only [nnrpow_def, NNReal.nnrpow_def, NNReal.coe_ofNat, NNReal.rpow_ofNat, pow_two]
  change cfcₙ (fun z : ℝ≥0 => id z * id z) a = a * a
  rw [cfcₙ_mul id id a, cfcₙ_id ℝ≥0 a]

lemma nnrpow_three (a : A) (ha : 0 ≤ a := by cfc_tac) : a ^ (3 : ℝ≥0) = a * a * a := by
  simp only [nnrpow_def, NNReal.nnrpow_def, NNReal.coe_ofNat, NNReal.rpow_ofNat, pow_three]
  change cfcₙ (fun z : ℝ≥0 => id z * (id z * id z)) a = a * a * a
  rw [cfcₙ_mul id _ a, cfcₙ_mul id _ a, ← mul_assoc, cfcₙ_id ℝ≥0 a]

@[simp]
lemma zero_nnrpow {x : ℝ≥0} : (0 : A) ^ x = 0 := by simp [nnrpow_def]

@[simp]
lemma nnrpow_nnrpow [UniqueNonUnitalContinuousFunctionalCalculus ℝ≥0 A]
    {a : A} {x y : ℝ≥0} : (a ^ x) ^ y = a ^ (x * y) := by
  by_cases ha : 0 ≤ a
  case pos =>
    obtain (rfl | hx) := eq_zero_or_pos x <;> obtain (rfl | hy) := eq_zero_or_pos y
    all_goals try simp
    simp only [nnrpow_def, NNReal.coe_mul]
    rw [← cfcₙ_comp _ _ a]
    congr! 2 with u
    ext
    simp [Real.rpow_mul]
  case neg =>
    simp [nnrpow_def, cfcₙ_apply_of_not_predicate a ha]

lemma nnrpow_nnrpow_inv [UniqueNonUnitalContinuousFunctionalCalculus ℝ≥0 A]
    (a : A) {x : ℝ≥0} (hx : x ≠ 0) (ha : 0 ≤ a := by cfc_tac) : (a ^ x) ^ x⁻¹ = a := by
  simp [mul_inv_cancel₀ hx, nnrpow_one _ ha]

lemma nnrpow_inv_nnrpow [UniqueNonUnitalContinuousFunctionalCalculus ℝ≥0 A]
    (a : A) {x : ℝ≥0} (hx : x ≠ 0) (ha : 0 ≤ a := by cfc_tac) : (a ^ x⁻¹) ^ x = a := by
  simp [inv_mul_cancel₀ hx, nnrpow_one _ ha]

lemma nnrpow_inv_eq [UniqueNonUnitalContinuousFunctionalCalculus ℝ≥0 A]
    (a b : A) {x : ℝ≥0} (hx : x ≠ 0) (ha : 0 ≤ a := by cfc_tac) (hb : 0 ≤ b := by cfc_tac) :
    a ^ x⁻¹ = b ↔ b ^ x = a :=
  ⟨fun h ↦ nnrpow_inv_nnrpow a hx ▸ congr($(h) ^ x).symm,
    fun h ↦ nnrpow_nnrpow_inv b hx ▸ congr($(h) ^ x⁻¹).symm⟩

section sqrt

noncomputable def sqrt (a : A) : A := cfcₙ NNReal.sqrt a

@[simp]
lemma sqrt_nonneg {a : A} : 0 ≤ sqrt a := cfcₙ_predicate _ a

lemma sqrt_eq_nnrpow {a : A} : sqrt a = a ^ (1 / 2 : ℝ≥0) := by
  simp only [sqrt, nnrpow, NNReal.coe_inv, NNReal.coe_ofNat, NNReal.rpow_eq_pow]
  congr
  ext
  exact_mod_cast NNReal.sqrt_eq_rpow _

@[simp]
lemma sqrt_zero : sqrt (0 : A) = 0 := by simp [sqrt]

variable [UniqueNonUnitalContinuousFunctionalCalculus ℝ≥0 A]

@[simp]
lemma nnrpow_sqrt {a : A} {x : ℝ≥0} : (sqrt a) ^ x = a ^ (x / 2) := by
  rw [sqrt_eq_nnrpow, nnrpow_nnrpow, one_div_mul_eq_div 2 x]

lemma nnrpow_sqrt_two (a : A) (ha : 0 ≤ a := by cfc_tac) : (sqrt a) ^ (2 : ℝ≥0) = a := by
  simp only [nnrpow_sqrt, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_self]
  rw [nnrpow_one a]

lemma sqrt_mul_sqrt_self (a : A) (ha : 0 ≤ a := by cfc_tac) : sqrt a * sqrt a = a := by
  rw [← nnrpow_two _, nnrpow_sqrt_two _]

@[simp]
lemma sqrt_nnrpow {a : A} {x : ℝ≥0} : sqrt (a ^ x) = a ^ (x / 2) := by
  simp [sqrt_eq_nnrpow, div_eq_mul_inv]

lemma sqrt_nnrpow_two (a : A) (ha : 0 ≤ a := by cfc_tac) : sqrt (a ^ (2 : ℝ≥0)) = a := by
  simp only [sqrt_nnrpow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_self]
  rw [nnrpow_one _]

lemma sqrt_mul_self (a : A) (ha : 0 ≤ a := by cfc_tac) : sqrt (a * a) = a := by
  rw [← nnrpow_two _, sqrt_nnrpow_two _]

lemma mul_self_eq {a b : A} (h : sqrt a = b) (ha : 0 ≤ a := by cfc_tac) :
    b * b = a :=
  h ▸ sqrt_mul_sqrt_self _ ha

lemma sqrt_unique {a b : A} (h : b * b = a) (hb : 0 ≤ b := by cfc_tac) :
    sqrt a = b :=
  h ▸ sqrt_mul_self b

lemma sqrt_eq_iff (a b : A) (ha : 0 ≤ a := by cfc_tac) (hb : 0 ≤ b := by cfc_tac) :
    sqrt a = b ↔ b * b = a :=
  ⟨(mul_self_eq ·), (sqrt_unique ·)⟩

lemma sqrt_eq_zero_iff (a : A) (ha : 0 ≤ a := by cfc_tac) : sqrt a = 0 ↔ a = 0 := by
  rw [sqrt_eq_iff a _, mul_zero, eq_comm]

end sqrt

end NonUnital

section Unital

variable {A : Type*} [PartialOrder A] [NormedRing A] [StarRing A]
  [NormedAlgebra ℝ A] [ContinuousFunctionalCalculus ℝ≥0 (fun (a : A) => 0 ≤ a)]

noncomputable def rpow (a : A) (y : ℝ) : A := cfc (fun x : ℝ≥0 => x ^ y) a

noncomputable instance (priority := 100) : Pow A ℝ where
  pow a y := rpow a y

@[simp]
lemma rpow_eq_pow {a : A} {y : ℝ} : rpow a y = a ^ y := rfl

@[simp]
lemma rpow_nonneg {a : A} {y : ℝ} : 0 ≤ a ^ y := cfc_predicate _ a

lemma rpow_def {a : A} {y : ℝ} : a ^ y = cfc (fun x : ℝ≥0 => x ^ y) a := rfl

lemma rpow_one (a : A) (ha : 0 ≤ a := by cfc_tac) : a ^ (1 : ℝ) = a := by
  simp only [rpow_def, NNReal.coe_one, NNReal.rpow_eq_pow, NNReal.rpow_one, cfc_id' ℝ≥0 a]

@[simp]
lemma one_rpow {x : ℝ} : (1 : A) ^ x = (1 : A) := by simp [rpow_def]

lemma rpow_zero (a : A) (ha : 0 ≤ a := by cfc_tac) : a ^ (0 : ℝ) = 1 := by
  simp [rpow_def, cfc_const_one ℝ≥0 a]

lemma zero_rpow {x : ℝ} (hx : x ≠ 0) : rpow (0 : A) x = 0 := by simp [rpow, NNReal.zero_rpow hx]

lemma rpow_natCast (a : A) (n : ℕ) (ha : 0 ≤ a := by cfc_tac) : a ^ (n : ℝ) = a ^ n := by
  rw [← cfc_pow_id (R := ℝ≥0) a n, rpow_def]
  congr
  simp

@[simp]
lemma rpow_algebraMap {x : ℝ≥0} {y : ℝ} :
    (algebraMap ℝ≥0 A x) ^ y = algebraMap ℝ≥0 A (x ^ y) := by
  rw [rpow_def, cfc_algebraMap ..]

lemma rpow_add {a : A} {x y : ℝ} (ha : 0 ∉ spectrum ℝ≥0 a) :
    a ^ (x + y) = a ^ x * a ^ y := by
  simp only [rpow_def, NNReal.rpow_eq_pow]
  rw [← cfc_mul _ _ a]
  refine cfc_congr ?_
  intro z hz
  have : z ≠ 0 := by aesop
  simp [NNReal.rpow_add this _ _]

lemma rpow_rpow [UniqueContinuousFunctionalCalculus ℝ≥0 A]
    (a : A) (x y : ℝ) (ha₁ : 0 ∉ spectrum ℝ≥0 a) (hx : x ≠ 0) (ha₂ : 0 ≤ a := by cfc_tac) :
    (a ^ x) ^ y = a ^ (x * y) := by
  simp only [rpow_def]
  rw [← cfc_comp _ _ a ha₂]
  refine cfc_congr fun _ _ => ?_
  simp [NNReal.rpow_mul]

lemma rpow_rpow_of_exponent_nonneg [UniqueContinuousFunctionalCalculus ℝ≥0 A] (a : A) (x y : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (ha₂ : 0 ≤ a := by cfc_tac) : (a ^ x) ^ y = a ^ (x * y) := by
  simp only [rpow_def]
  rw [← cfc_comp _ _ a]
  refine cfc_congr fun _ _ => ?_
  simp [NNReal.rpow_mul]

lemma rpow_mul_rpow_neg {a : A} (x : ℝ) (ha : 0 ∉ spectrum ℝ≥0 a)
    (ha' : 0 ≤ a := by cfc_tac) : a ^ x * a ^ (-x) = 1 := by
  rw [← rpow_add ha, add_neg_cancel, rpow_zero a]

lemma rpow_neg_mul_rpow {a : A} (x : ℝ) (ha : 0 ∉ spectrum ℝ≥0 a)
    (ha' : 0 ≤ a := by cfc_tac) : a ^ (-x) * a ^ x = 1 := by
  rw [← rpow_add ha, neg_add_cancel, rpow_zero a]

lemma rpow_neg_one_eq_inv (a : Aˣ) (ha : (0 : A) ≤ a := by cfc_tac) :
    a ^ (-1 : ℝ) = (↑a⁻¹ : A) := by
  refine a.inv_eq_of_mul_eq_one_left ?_ |>.symm
  simpa [rpow_one (a : A)] using rpow_neg_mul_rpow 1 (spectrum.zero_not_mem ℝ≥0 a.isUnit)

lemma rpow_neg_one_eq_cfc_inv {A : Type*} [PartialOrder A] [NormedRing A] [StarRing A]
    [NormedAlgebra ℝ A] [ContinuousFunctionalCalculus ℝ≥0 ((0 : A) ≤ ·)] (a : A) :
    a ^ (-1 : ℝ) = cfc (·⁻¹ : ℝ≥0 → ℝ≥0) a :=
  cfc_congr fun x _ ↦ NNReal.rpow_neg_one x

lemma rpow_neg [UniqueContinuousFunctionalCalculus ℝ≥0 A] (a : Aˣ) (x : ℝ)
    (ha' : (0 : A) ≤ a := by cfc_tac) : (a : A) ^ (-x) = (↑a⁻¹ : A) ^ x := by
  suffices h₁ : ContinuousOn (fun z ↦ z ^ x) (Inv.inv '' (spectrum ℝ≥0 (a : A))) by
    rw [← cfc_inv_id (R := ℝ≥0) a, rpow_def, rpow_def,
        ← cfc_comp' (fun z => z ^ x) (Inv.inv : ℝ≥0 → ℝ≥0) (a : A) h₁]
    refine cfc_congr fun _ _ => ?_
    simp [NNReal.rpow_neg, NNReal.inv_rpow]
  refine NNReal.continuousOn_rpow_const (.inl ?_)
  rintro ⟨z, hz, hz'⟩
  exact spectrum.zero_not_mem ℝ≥0 a.isUnit <| inv_eq_zero.mp hz' ▸ hz

lemma rpow_intCast (a : Aˣ) (n : ℤ) (ha : (0 : A) ≤ a := by cfc_tac) :
    (a : A) ^ (n : ℝ) = (↑(a ^ n) : A) := by
  rw [← cfc_zpow (R := ℝ≥0) a n, rpow_def]
  refine cfc_congr fun _ _ => ?_
  simp

section unital_vs_nonunital

variable [UniqueNonUnitalContinuousFunctionalCalculus ℝ≥0 A]

open scoped ContinuousFunctionalCalculus

lemma nnrpow_eq_rpow {a : A} {x : ℝ≥0} (hx : 0 < x) : a ^ x = a ^ (x : ℝ) := by
  rw [nnrpow_def (A := A), rpow_def, cfcₙ_eq_cfc]

lemma sqrt_eq_rpow {a : A} : sqrt a = a ^ (1 / 2 : ℝ) := by
  have : a ^ (1 / 2 : ℝ) = a ^ ((1 / 2 : ℝ≥0) : ℝ) := rfl
  rw [this, ← nnrpow_eq_rpow (by norm_num), sqrt_eq_nnrpow (A := A)]

lemma sqrt_eq_cfc {a : A} : sqrt a = cfc NNReal.sqrt a := by
  unfold sqrt
  rw [cfcₙ_eq_cfc]

lemma sqrt_sq (a : A) (ha : 0 ≤ a := by cfc_tac) : sqrt (a ^ 2) = a := by
  rw [pow_two, sqrt_mul_self (A := A) a]

lemma sq_sqrt (a : A) (ha : 0 ≤ a := by cfc_tac) : (sqrt a) ^ 2 = a := by
  rw [pow_two, sqrt_mul_sqrt_self (A := A) a]

@[simp]
lemma sqrt_algebraMap {r : ℝ≥0} : sqrt (algebraMap ℝ≥0 A r) = algebraMap ℝ≥0 A (NNReal.sqrt r) := by
  rw [sqrt_eq_cfc, cfc_algebraMap]

@[simp]
lemma sqrt_one : sqrt (1 : A) = 1 := by simp [sqrt_eq_cfc]

lemma sqrt_rpow [UniqueContinuousFunctionalCalculus ℝ≥0 A] {a : A} {x : ℝ} (h : 0 ∉ spectrum ℝ≥0 a)
    (hx : x ≠ 0) : sqrt (a ^ x) = a ^ (x / 2) := by
  by_cases hnonneg : 0 ≤ a
  case pos =>
    simp only [sqrt_eq_rpow, div_eq_mul_inv, one_mul, rpow_rpow _ _ _ h hx]
  case neg =>
    simp [sqrt_eq_cfc, rpow_def, cfc_apply_of_not_predicate a hnonneg]

lemma rpow_sqrt [UniqueContinuousFunctionalCalculus ℝ≥0 A] (a : A) (x : ℝ) (h : 0 ∉ spectrum ℝ≥0 a)
    (ha : 0 ≤ a := by cfc_tac) : (sqrt a) ^ x = a ^ (x / 2) := by
  rw [sqrt_eq_rpow, div_eq_mul_inv, one_mul,
      rpow_rpow _ _ _ h (by norm_num), inv_mul_eq_div]

end unital_vs_nonunital

end Unital

end CFC
