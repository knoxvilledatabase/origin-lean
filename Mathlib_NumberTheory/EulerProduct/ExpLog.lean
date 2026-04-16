/-
Extracted from NumberTheory/EulerProduct/ExpLog.lean
Genuine: 2 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Data.Complex.FiniteDimensional
import Mathlib.NumberTheory.EulerProduct.Basic

noncomputable section

/-!
# Logarithms of Euler Products

We consider `f : ℕ →*₀ ℂ` and show that `exp (∑ p in Primes, log (1 - f p)⁻¹) = ∑ n : ℕ, f n`
under suitable conditions on `f`. This can be seen as a logarithmic version of the
Euler product for `f`.
-/

open Complex

open Topology in

lemma Summable.clog_one_sub {α  : Type*} {f : α → ℂ} (hsum : Summable f) :
    Summable fun n ↦ log (1 - f n) := by
  have hg : DifferentiableAt ℂ (fun z ↦ log (1 - z)) 0 := by
    have : 1 - 0 ∈ slitPlane := (sub_zero (1 : ℂ)).symm ▸ one_mem_slitPlane
    fun_prop (disch := assumption)
  have : (fun z ↦ log (1 - z)) =O[𝓝 0] id := by
    simpa only [sub_zero, log_one] using hg.isBigO_sub
  exact this.comp_summable hsum

namespace EulerProduct

theorem exp_tsum_primes_log_eq_tsum {f : ℕ →*₀ ℂ} (hsum : Summable (‖f ·‖)) :
    exp (∑' p : Nat.Primes, -log (1 - f p)) = ∑' n : ℕ, f n := by
  have hs {p : ℕ} (hp : 1 < p) : ‖f p‖ < 1 := hsum.of_norm.norm_lt_one (f := f.toMonoidHom) hp
  have hp (p : Nat.Primes) : 1 - f p ≠ 0 :=
    fun h ↦ (norm_one (α := ℂ) ▸ (sub_eq_zero.mp h) ▸ hs p.prop.one_lt).false
  have H := hsum.of_norm.clog_one_sub.neg.subtype {p | p.Prime} |>.hasSum.cexp.tprod_eq
  simp only [Set.coe_setOf, Set.mem_setOf_eq, Function.comp_apply, exp_neg, exp_log (hp _)] at H
  exact H.symm.trans <| eulerProduct_completely_multiplicative_tprod hsum

end EulerProduct
