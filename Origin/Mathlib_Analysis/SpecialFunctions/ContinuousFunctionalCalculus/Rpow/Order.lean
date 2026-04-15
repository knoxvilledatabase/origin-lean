/-
Extracted from Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Order.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Order properties of `CFC.rpow`

This file shows that `a ↦ a ^ p` is monotone for `p ∈ [0, 1]`, where `a` is an element of a
C⋆-algebra. The proof makes use of the integral representation of `rpow` in
`Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation`.

## Main declarations

+ `CFC.monotone_nnrpow`, `CFC.monotone_rpow`: `a ↦ a ^ p` is operator monotone for `p ∈ [0,1]`
+ `CFC.monotone_sqrt`: `CFC.sqrt` is operator monotone

## TODO

+ Show operator concavity of `rpow` over `Icc 0 1`
+ Show that `rpow` over `Icc (-1) 0` is operator antitone and operator convex
+ Show operator convexity of `rpow` over `Icc 1 2`

## References

+ [carlen2010] Eric A. Carlen, "Trace inequalities and quantum entropies: An introductory course"
  (see Lemma 2.8)
-/

open Set

open scoped NNReal

namespace CFC

section NonUnitalCStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open Real MeasureTheory

private lemma monotoneOn_nnrpow_Ioo {p : ℝ≥0} (hp : p ∈ Ioo 0 1) :
    MonotoneOn (fun a : A => a ^ p) (Ici 0) := by
  obtain ⟨μ, hμ⟩ := CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₀₁ A hp
  have h₃' : (Ici 0).EqOn (fun a : A => a ^ p)
      (fun a : A => ∫ t in Ioi 0, cfcₙ (rpowIntegrand₀₁ p t) a ∂μ) :=
    fun a ha => (hμ a ha).2
  refine MonotoneOn.congr ?_ h₃'.symm
  refine integral_monotoneOn_of_integrand_ae ?_ fun a ha => (hμ a ha).1
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact monotoneOn_cfcₙ_rpowIntegrand₀₁ hp ht

lemma monotone_nnrpow {p : ℝ≥0} (hp : p ∈ Icc 0 1) :
    Monotone (fun a : A => a ^ p) := by
  intro a b hab
  by_cases ha : 0 ≤ a
  · have hb : 0 ≤ b := ha.trans hab
    have hIcc : Icc (0 : ℝ≥0) 1 = Ioo 0 1 ∪ {0} ∪ {1} := by ext; simp
    rw [hIcc] at hp
    obtain (hp | hp) | hp := hp
    · exact monotoneOn_nnrpow_Ioo hp ha hb hab
    · simp_all [mem_singleton_iff]
    · simp_all [mem_singleton_iff, nnrpow_one a, nnrpow_one b]
  · have : a ^ p = 0 := cfcₙ_apply_of_not_predicate a ha
    simp [this]

lemma monotone_sqrt : Monotone (sqrt : A → A) := by
  intro a b hab
  rw [CFC.sqrt_eq_nnrpow a, CFC.sqrt_eq_nnrpow b]
  refine (monotone_nnrpow (A := A) ?_) hab
  constructor <;> norm_num
