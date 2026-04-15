/-
Extracted from Analysis/SpecificLimits/Fibonacci.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The ratio of consecutive Fibonacci numbers

We prove that the ratio of consecutive Fibonacci numbers tends to the golden ratio.
-/

open Nat Real Filter Tendsto

open scoped Topology goldenRatio

theorem tendsto_fib_succ_div_fib_atTop :
    Tendsto (fun n ↦ (fib (n + 1) / fib n : ℝ)) atTop (𝓝 φ) := by
  have h₁ n : (fib (n + 1) / fib n : ℝ) = (φ - ψ * (ψ / φ) ^ n) / (1 - (ψ / φ) ^ n) := by
    simp only [coe_fib_eq, pow_succ, div_pow]
    field
  have h₂ := tendsto_pow_atTop_nhds_zero_of_abs_lt_one (r := ψ / φ) <| by
    rw [abs_div, div_lt_one <| by positivity, abs_of_pos goldenRatio_pos, abs_lt]
    ring_nf
    bound
  rw [show φ = (φ - ψ * 0) / (1 - 0) by ring, funext h₁]
  exact const_sub _ (const_mul _ h₂) |>.div (const_sub _ h₂) <| by simp

theorem tendsto_fib_div_fib_succ_atTop :
    Tendsto (fun n ↦ (fib n / fib (n + 1) : ℝ)) atTop (𝓝 (-ψ)) := by
  convert tendsto_fib_succ_div_fib_atTop.inv₀ (by positivity) using 2
  · rw [inv_div]
  · rw [inv_goldenRatio]
