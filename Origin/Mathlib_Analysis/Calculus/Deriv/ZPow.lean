/-
Extracted from Analysis/Calculus/Deriv/ZPow.lean
Genuine: 9 of 19 | Dissolved: 10 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Derivatives of `x ^ m`, `m : ℤ`

In this file we prove theorems about (iterated) derivatives of `x ^ m`, `m : ℤ`.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`analysis/calculus/deriv/basic`.

## Keywords

derivative, power
-/

universe u v w

open scoped Classical

open Topology Filter

open Filter Asymptotics Set

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

variable {x : 𝕜}

variable {s : Set 𝕜}

variable {m : ℤ}

/-! ### Derivative of `x ↦ x^m` for `m : ℤ` -/

-- DISSOLVED: hasStrictDerivAt_zpow

-- DISSOLVED: hasDerivAt_zpow

-- DISSOLVED: hasDerivWithinAt_zpow

-- DISSOLVED: differentiableAt_zpow

-- DISSOLVED: differentiableWithinAt_zpow

theorem differentiableOn_zpow (m : ℤ) (s : Set 𝕜) (h : (0 : 𝕜) ∉ s ∨ 0 ≤ m) :
    DifferentiableOn 𝕜 (fun x => x ^ m) s := fun x hxs =>
  differentiableWithinAt_zpow m x <| h.imp_left <| ne_of_mem_of_not_mem hxs

theorem deriv_zpow (m : ℤ) (x : 𝕜) : deriv (fun x => x ^ m) x = m * x ^ (m - 1) := by
  by_cases H : x ≠ 0 ∨ 0 ≤ m
  · exact (hasDerivAt_zpow m x H).deriv
  · rw [deriv_zero_of_not_differentiableAt (mt differentiableAt_zpow.1 H)]
    push_neg at H
    rcases H with ⟨rfl, hm⟩
    rw [zero_zpow _ ((sub_one_lt _).trans hm).ne, mul_zero]

@[simp]
theorem deriv_zpow' (m : ℤ) : (deriv fun x : 𝕜 => x ^ m) = fun x => (m : 𝕜) * x ^ (m - 1) :=
  funext <| deriv_zpow m

-- DISSOLVED: derivWithin_zpow

@[simp]
theorem iter_deriv_zpow' (m : ℤ) (k : ℕ) :
    (deriv^[k] fun x : 𝕜 => x ^ m) =
      fun x => (∏ i ∈ Finset.range k, ((m : 𝕜) - i)) * x ^ (m - k) := by
  induction' k with k ihk
  · simp only [one_mul, Int.ofNat_zero, id, sub_zero, Finset.prod_range_zero,
      Function.iterate_zero]
  · simp only [Function.iterate_succ_apply', ihk, deriv_const_mul_field', deriv_zpow',
      Finset.prod_range_succ, Int.ofNat_succ, ← sub_sub, Int.cast_sub, Int.cast_natCast, mul_assoc]

theorem iter_deriv_zpow (m : ℤ) (x : 𝕜) (k : ℕ) :
    deriv^[k] (fun y => y ^ m) x = (∏ i ∈ Finset.range k, ((m : 𝕜) - i)) * x ^ (m - k) :=
  congr_fun (iter_deriv_zpow' m k) x

theorem iter_deriv_pow (n : ℕ) (x : 𝕜) (k : ℕ) :
    deriv^[k] (fun x : 𝕜 => x ^ n) x = (∏ i ∈ Finset.range k, ((n : 𝕜) - i)) * x ^ (n - k) := by
  simp only [← zpow_natCast, iter_deriv_zpow, Int.cast_natCast]
  rcases le_or_lt k n with hkn | hnk
  · rw [Int.ofNat_sub hkn]
  · have : (∏ i ∈ Finset.range k, (n - i : 𝕜)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_range.2 hnk) (sub_self _)
    simp only [this, zero_mul]

@[simp]
theorem iter_deriv_pow' (n k : ℕ) :
    (deriv^[k] fun x : 𝕜 => x ^ n) =
      fun x => (∏ i ∈ Finset.range k, ((n : 𝕜) - i)) * x ^ (n - k) :=
  funext fun x => iter_deriv_pow n x k

theorem iter_deriv_inv (k : ℕ) (x : 𝕜) :
    deriv^[k] Inv.inv x = (∏ i ∈ Finset.range k, (-1 - i : 𝕜)) * x ^ (-1 - k : ℤ) := by
  simpa only [zpow_neg_one, Int.cast_neg, Int.cast_one] using iter_deriv_zpow (-1) x k

@[simp]
theorem iter_deriv_inv' (k : ℕ) :
    deriv^[k] Inv.inv = fun x : 𝕜 => (∏ i ∈ Finset.range k, (-1 - i : 𝕜)) * x ^ (-1 - k : ℤ) :=
  funext (iter_deriv_inv k)

variable {f : E → 𝕜} {t : Set E} {a : E}

-- DISSOLVED: DifferentiableWithinAt.zpow

-- DISSOLVED: DifferentiableAt.zpow

-- DISSOLVED: DifferentiableOn.zpow

-- DISSOLVED: Differentiable.zpow
