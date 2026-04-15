/-
Extracted from Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog/Basic.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The exponential and logarithm based on the continuous functional calculus

This file defines the logarithm via the continuous functional calculus (CFC) and builds its API.
This allows one to take logs of matrices, operators, elements of a C⋆-algebra, etc.

It also shows that exponentials defined via the continuous functional calculus are equal to
`NormedSpace.exp` (defined via power series) whenever the former are not junk values.

## Main declarations

+ `CFC.log`: the real log function based on the CFC, i.e. `cfc Real.log`
+ `CFC.exp_eq_normedSpace_exp`: exponentials based on the CFC are equal to exponentials based
  on power series.
+ `CFC.log_exp` and `CFC.exp_log`: `CFC.log` and `NormedSpace.exp ℝ` are inverses of each other.

## Implementation notes

Since `cfc Real.exp` and `cfc Complex.exp` are strictly less general than `NormedSpace.exp`
(defined via power series), we only give minimal API for these here in order to relate
`NormedSpace.exp` to functions defined via the CFC. In particular, we don't give separate
definitions for them.

## TODO

+ Show that `log (a * b) = log a + log b` whenever `a` and `b` commute (and the same for indexed
  products).
+ Relate `CFC.log` to `rpow`, `zpow`, `sqrt`, `inv`.
-/

open NormedSpace

section general_exponential

variable {𝕜 : Type*} {α : Type*} [RCLike 𝕜] [TopologicalSpace α] [CompactSpace α]

lemma NormedSpace.exp_continuousMap_eq (f : C(α, 𝕜)) :
    exp f = (⟨exp ∘ f, exp_continuous.comp f.continuous⟩ : C(α, 𝕜)) := by
  ext a
  simp_rw [NormedSpace.exp_eq_expSeries_sum (𝔸 := C(α, 𝕜)) 𝕜, FormalMultilinearSeries.sum]
  have h_sum := NormedSpace.expSeries_summable (𝕂 := 𝕜) f
  simp_rw [← ContinuousMap.tsum_apply h_sum a, NormedSpace.expSeries_apply_eq]
  simp [NormedSpace.exp_eq_tsum 𝕜]

end general_exponential

namespace CFC

section RCLikeNormed

variable {𝕜 : Type*} {A : Type*} [RCLike 𝕜] {p : A → Prop} [NormedRing A]
  [StarRing A] [NormedAlgebra 𝕜 A] [ContinuousFunctionalCalculus 𝕜 A p]

open scoped ContinuousFunctionalCalculus in

lemma exp_eq_normedSpace_exp {a : A} (ha : p a := by cfc_tac) :
    cfc (exp : 𝕜 → 𝕜) a = exp a := by
  conv_rhs => rw [← cfc_id 𝕜 a ha, cfc_apply id a ha]
  have h := cfcHom_continuous (R := 𝕜) ha
  have _ : ContinuousOn exp (spectrum 𝕜 a) := exp_continuous.continuousOn
  let +nondep : Algebra ℚ A := .restrictScalars ℚ 𝕜 A
  simp_rw [← map_exp _ h, cfc_apply exp a ha]
  congr 1
  ext
  simp [exp_continuousMap_eq]

end RCLikeNormed

section RealNormed

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A]
  [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

lemma real_exp_eq_normedSpace_exp {a : A} (ha : IsSelfAdjoint a := by cfc_tac) :
    cfc Real.exp a = exp a :=
  Real.exp_eq_exp_ℝ ▸ exp_eq_normedSpace_exp ha
