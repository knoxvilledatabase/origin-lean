/-
Extracted from Analysis/SpecialFunctions/Bernstein.lean
Genuine: 14 | Conflates: 0 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.RingTheory.Polynomial.Bernstein
import Mathlib.Topology.ContinuousMap.Polynomial
import Mathlib.Topology.ContinuousMap.Compact

noncomputable section

/-!
# Bernstein approximations and Weierstrass' theorem

We prove that the Bernstein approximations
```
∑ k : Fin (n+1), f (k/n : ℝ) * n.choose k * x^k * (1-x)^(n-k)
```
for a continuous function `f : C([0,1], ℝ)` converge uniformly to `f` as `n` tends to infinity.

Our proof follows [Richard Beals' *Analysis, an introduction*][beals-analysis], §7D.
The original proof, due to [Bernstein](bernstein1912) in 1912, is probabilistic,
and relies on Bernoulli's theorem,
which gives bounds for how quickly the observed frequencies in a
Bernoulli trial approach the underlying probability.

The proof here does not directly rely on Bernoulli's theorem,
but can also be given a probabilistic account.
* Consider a weighted coin which with probability `x` produces heads,
  and with probability `1-x` produces tails.
* The value of `bernstein n k x` is the probability that
  such a coin gives exactly `k` heads in a sequence of `n` tosses.
* If such an appearance of `k` heads results in a payoff of `f(k / n)`,
  the `n`-th Bernstein approximation for `f` evaluated at `x` is the expected payoff.
* The main estimate in the proof bounds the probability that
  the observed frequency of heads differs from `x` by more than some `δ`,
  obtaining a bound of `(4 * n * δ^2)⁻¹`, irrespective of `x`.
* This ensures that for `n` large, the Bernstein approximation is (uniformly) close to the
  payoff function `f`.

(You don't need to think in these terms to follow the proof below: it's a giant `calc` block!)

This result proves Weierstrass' theorem that polynomials are dense in `C([0,1], ℝ)`,
although we defer an abstract statement of this until later.
-/

noncomputable section

open scoped BoundedContinuousFunction unitInterval

def bernstein (n ν : ℕ) : C(I, ℝ) :=
  (bernsteinPolynomial ℝ n ν).toContinuousMapOn I

@[simp]
theorem bernstein_apply (n ν : ℕ) (x : I) :
    bernstein n ν x = (n.choose ν : ℝ) * (x : ℝ) ^ ν * (1 - (x : ℝ)) ^ (n - ν) := by
  dsimp [bernstein, Polynomial.toContinuousMapOn, Polynomial.toContinuousMap, bernsteinPolynomial]
  simp

theorem bernstein_nonneg {n ν : ℕ} {x : I} : 0 ≤ bernstein n ν x := by
  simp only [bernstein_apply]
  have h₁ : (0 : ℝ) ≤ x := by unit_interval
  have h₂ : (0 : ℝ) ≤ 1 - x := by unit_interval
  positivity

namespace Mathlib.Meta.Positivity

open Lean Meta Qq Function

@[positivity DFunLike.coe _ _]
def evalBernstein : PositivityExt where eval {_ _} _zα _pα e := do
  let .app (.app _coe (.app (.app _ n) ν)) x ← whnfR e | throwError "not bernstein polynomial"
  let p ← mkAppOptM ``bernstein_nonneg #[n, ν, x]
  pure (.nonnegative p)

end Mathlib.Meta.Positivity

/-!
We now give a slight reformulation of `bernsteinPolynomial.variance`.
-/

namespace bernstein

def z {n : ℕ} (k : Fin (n + 1)) : I :=
  ⟨(k : ℝ) / n, by
    cases' n with n
    · norm_num
    · have h₁ : 0 < (n.succ : ℝ) := mod_cast Nat.succ_pos _
      have h₂ : ↑k ≤ n.succ := mod_cast Fin.le_last k
      rw [Set.mem_Icc, le_div_iff₀ h₁, div_le_iff₀ h₁]
      norm_cast
      simp [h₂]⟩

local postfix:90 "/ₙ" => z

theorem probability (n : ℕ) (x : I) : (∑ k : Fin (n + 1), bernstein n k x) = 1 := by
  have := bernsteinPolynomial.sum ℝ n
  apply_fun fun p => Polynomial.aeval (x : ℝ) p at this
  simp? [map_sum, Finset.sum_range] at this says
    simp only [Finset.sum_range, map_sum, Polynomial.coe_aeval_eq_eval, Polynomial.eval_one] at this
  exact this

theorem variance {n : ℕ} (h : 0 < (n : ℝ)) (x : I) :
    (∑ k : Fin (n + 1), (x - k/ₙ : ℝ) ^ 2 * bernstein n k x) = (x : ℝ) * (1 - x) / n := by
  have h' : (n : ℝ) ≠ 0 := ne_of_gt h
  apply_fun fun x : ℝ => x * n using GroupWithZero.mul_left_injective h'
  apply_fun fun x : ℝ => x * n using GroupWithZero.mul_left_injective h'
  dsimp
  conv_lhs => simp only [Finset.sum_mul, z]
  conv_rhs => rw [div_mul_cancel₀ _ h']
  have := bernsteinPolynomial.variance ℝ n
  apply_fun fun p => Polynomial.aeval (x : ℝ) p at this
  simp? [map_sum, Finset.sum_range, ← Polynomial.natCast_mul] at this says
    simp only [nsmul_eq_mul, Finset.sum_range, map_sum, Polynomial.coe_aeval_eq_eval,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_natCast,
      Polynomial.eval_X, Polynomial.eval_one] at this
  convert this using 1
  · congr 1; funext k
    rw [mul_comm _ (n : ℝ), mul_comm _ (n : ℝ), ← mul_assoc, ← mul_assoc]
    congr 1
    field_simp [h]
    ring
  · ring

end bernstein

open bernstein

local postfix:1024 "/ₙ" => z

def bernsteinApproximation (n : ℕ) (f : C(I, ℝ)) : C(I, ℝ) :=
  ∑ k : Fin (n + 1), f k/ₙ • bernstein n k

/-!
We now set up some of the basic machinery of the proof that the Bernstein approximations
converge uniformly.

A key player is the set `S f ε h n x`,
for some function `f : C(I, ℝ)`, `h : 0 < ε`, `n : ℕ` and `x : I`.

This is the set of points `k` in `Fin (n+1)` such that
`k/n` is within `δ` of `x`, where `δ` is the modulus of uniform continuity for `f`,
chosen so `|f x - f y| < ε/2` when `|x - y| < δ`.

We show that if `k ∉ S`, then `1 ≤ δ^-2 * (x - k/n)^2`.
-/

namespace bernsteinApproximation

@[simp]
theorem apply (n : ℕ) (f : C(I, ℝ)) (x : I) :
    bernsteinApproximation n f x = ∑ k : Fin (n + 1), f k/ₙ * bernstein n k x := by
  simp [bernsteinApproximation]

def δ (f : C(I, ℝ)) (ε : ℝ) (h : 0 < ε) : ℝ :=
  f.modulus (ε / 2) (half_pos h)

theorem δ_pos {f : C(I, ℝ)} {ε : ℝ} {h : 0 < ε} : 0 < δ f ε h :=
  f.modulus_pos

def S (f : C(I, ℝ)) (ε : ℝ) (h : 0 < ε) (n : ℕ) (x : I) : Finset (Fin (n + 1)) :=
  {k : Fin (n + 1) | dist k/ₙ x < δ f ε h}.toFinset

theorem lt_of_mem_S {f : C(I, ℝ)} {ε : ℝ} {h : 0 < ε} {n : ℕ} {x : I} {k : Fin (n + 1)}
    (m : k ∈ S f ε h n x) : |f k/ₙ - f x| < ε / 2 := by
  apply f.dist_lt_of_dist_lt_modulus (ε / 2) (half_pos h)
  -- Porting note: `simp` fails to apply `Set.mem_toFinset` on its own
  simpa [S, (Set.mem_toFinset)] using m

theorem le_of_mem_S_compl {f : C(I, ℝ)} {ε : ℝ} {h : 0 < ε} {n : ℕ} {x : I} {k : Fin (n + 1)}
    (m : k ∈ (S f ε h n x)ᶜ) : (1 : ℝ) ≤ δ f ε h ^ (-2 : ℤ) * ((x : ℝ) - k/ₙ) ^ 2 := by
  -- Porting note: added parentheses to help `simp`
  simp only [Finset.mem_compl, not_lt, Set.mem_toFinset, Set.mem_setOf_eq, S] at m
  rw [zpow_neg, ← div_eq_inv_mul, zpow_two, ← pow_two, one_le_div (pow_pos δ_pos 2), sq_le_sq,
    abs_of_pos δ_pos]
  rwa [dist_comm] at m

end bernsteinApproximation

open bernsteinApproximation

open BoundedContinuousFunction

open Filter

open scoped Topology
