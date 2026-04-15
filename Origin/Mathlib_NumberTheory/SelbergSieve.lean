/-
Extracted from NumberTheory/SelbergSieve.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The Selberg Sieve

We set up the working assumptions of the Selberg sieve, define the notion of an upper bound sieve
and show that every upper bound sieve yields an upper bound on the size of the sifted set. We also
define the Λ² sieve and prove that Λ² sieves are upper bound sieves. We then diagonalise the main
term of the Λ² sieve.

We mostly follow the treatment outlined by Heath-Brown in the notes to an old graduate course. One
minor notational difference is that we write $\nu(n)$ in place of $\frac{\omega(n)}{n}$.

## Results
* `siftedSum_le_mainSum_errSum_of_UpperBoundSieve` - Every upper bound sieve gives an upper bound
  on the size of the sifted set in terms of `mainSum` and `errSum`

## References

* [Heath-Brown, *Lectures on sieves*][heathbrown2002lecturessieves]
* [Koukoulopoulos, *The Distribution of Prime Numbers*][MR3971232]

-/

noncomputable section

open scoped ArithmeticFunction

open Finset Real Nat

structure BoundingSieve where
  /-- The set of natural numbers that is to be sifted. The fundamental lemma yields an upper bound
  on the size of this set after the multiples of small primes have been removed. -/
  support : Finset ℕ
  /-- The finite set of prime numbers whose multiples are to be sifted from `support`. We work with
  their product because it lets us treat `nu` as a multiplicative arithmetic function. It also
  plays well with Moebius inversion. -/
  prodPrimes : ℕ
  prodPrimes_squarefree : Squarefree prodPrimes
  /-- A sequence representing how much each element of `support` should be weighted. -/
  weights : ℕ → ℝ
  weights_nonneg : ∀ n : ℕ, 0 ≤ weights n
  /-- An approximation to `∑ i in support, weights i`, i.e. the size of the unsifted set. A bad
  approximation will yield a weak statement in the final theorem. -/
  totalMass : ℝ
  /-- `nu d` is an approximation to the proportion of elements of `support` that are a multiple of
  `d` -/
  nu : ArithmeticFunction ℝ
  nu_mult : nu.IsMultiplicative
  nu_pos_of_prime : ∀ p : ℕ, p.Prime → p ∣ prodPrimes → 0 < nu p
  nu_lt_one_of_prime : ∀ p : ℕ, p.Prime → p ∣ prodPrimes → nu p < 1

structure SelbergSieve extends BoundingSieve where
  /-- The `level` of the sieve controls how many terms we include in the inclusion-exclusion type
  sum. A higher level will yield a tighter bound for the main term, but will also increase the
  size of the error term. -/
  level : ℝ
  one_le_level : 1 ≤ level

attribute [arith_mult] BoundingSieve.nu_mult

namespace Mathlib.Meta.Positivity

open Lean Meta Qq
