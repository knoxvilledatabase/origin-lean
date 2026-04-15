/-
Extracted from Analysis/Calculus/LogDeriv.lean
Genuine: 11 of 17 | Dissolved: 5 | Infrastructure: 1
-/
import Origin.Core
import Mathlib.Analysis.Calculus.Deriv.ZPow

/-!
# Logarithmic Derivatives

We define the logarithmic derivative of a function f as `deriv f / f`. We then prove some basic
facts about this, including how it changes under multiplication and composition.

-/

noncomputable section

open Filter Function

open scoped Topology Classical

variable {𝕜 𝕜': Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜']

def logDeriv (f : 𝕜 → 𝕜') :=
  deriv f / f

theorem logDeriv_apply (f : 𝕜 → 𝕜') (x : 𝕜) : logDeriv f x = deriv f x / f x := rfl

lemma logDeriv_eq_zero_of_not_differentiableAt (f : 𝕜 → 𝕜') (x : 𝕜) (h : ¬DifferentiableAt 𝕜 f x) :
    logDeriv f x = 0 := by
  simp only [logDeriv_apply, deriv_zero_of_not_differentiableAt h, zero_div]

@[simp]
theorem logDeriv_id (x : 𝕜) : logDeriv id x = 1 / x := by
  simp [logDeriv_apply]

@[simp] theorem logDeriv_id' (x : 𝕜) : logDeriv (·) x = 1 / x := logDeriv_id x

@[simp]
theorem logDeriv_const (a : 𝕜') : logDeriv (fun _ : 𝕜 ↦ a) = 0 := by
  ext
  simp [logDeriv_apply]

-- DISSOLVED: logDeriv_mul

-- DISSOLVED: logDeriv_div

-- DISSOLVED: logDeriv_mul_const

-- DISSOLVED: logDeriv_const_mul

-- DISSOLVED: logDeriv_prod

lemma logDeriv_fun_zpow {f : 𝕜 → 𝕜'} {x : 𝕜} (hdf : DifferentiableAt 𝕜 f x) (n : ℤ) :
    logDeriv (f · ^ n) x = n * logDeriv f x := by
  rcases eq_or_ne n 0 with rfl | hn; · simp
  rcases eq_or_ne (f x) 0 with hf | hf
  · simp [logDeriv_apply, zero_zpow, *]
  · rw [logDeriv_apply, ← comp_def (·^n), deriv_comp _ (differentiableAt_zpow.2 <| .inl hf) hdf,
      deriv_zpow, logDeriv_apply]
    field_simp [zpow_ne_zero, zpow_sub_one₀ hf]
    ring

lemma logDeriv_fun_pow {f : 𝕜 → 𝕜'} {x : 𝕜} (hdf : DifferentiableAt 𝕜 f x) (n : ℕ) :
    logDeriv (f · ^ n) x = n * logDeriv f x :=
  mod_cast logDeriv_fun_zpow hdf n

@[simp]
lemma logDeriv_zpow (x : 𝕜) (n : ℤ) : logDeriv (· ^ n) x = n / x := by
  rw [logDeriv_fun_zpow (by fun_prop), logDeriv_id', mul_one_div]

@[simp]
lemma logDeriv_pow (x : 𝕜) (n : ℕ) : logDeriv (· ^ n) x = n / x :=
  mod_cast logDeriv_zpow x n

@[simp] lemma logDeriv_inv (x : 𝕜) : logDeriv (·⁻¹) x = -1 / x := by
  simpa using logDeriv_zpow x (-1)

theorem logDeriv_comp {f : 𝕜' → 𝕜'} {g : 𝕜 → 𝕜'} {x : 𝕜} (hf : DifferentiableAt 𝕜' f (g x))
    (hg : DifferentiableAt 𝕜 g x) : logDeriv (f ∘ g) x = logDeriv f (g x) * deriv g x := by
  simp only [logDeriv, Pi.div_apply, deriv_comp _ hf hg, comp_apply]
  ring
