/-
Extracted from Algebra/Polynomial/Reverse.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Reverse of a univariate polynomial

The main definition is `reverse`.  Applying `reverse` to a polynomial `f : R[X]` produces
the polynomial with a reversed list of coefficients, equivalent to `X^f.natDegree * f(1/X)`.

The main result is that `reverse (f * g) = reverse f * reverse g`, provided the leading
coefficients of `f` and `g` do not multiply to zero.
-/

namespace Polynomial

open Finsupp Finset

open scoped Polynomial

section Semiring

variable {R : Type*} [Semiring R] {f : R[X]}

def revAtFun (N i : ℕ) : ℕ :=
  ite (i ≤ N) (N - i) i

theorem revAtFun_invol {N i : ℕ} : revAtFun N (revAtFun N i) = i := by
  unfold revAtFun
  grind

theorem revAtFun_inj {N : ℕ} : Function.Injective (revAtFun N) := by
  intro a b hab
  rw [← @revAtFun_invol N a, hab, revAtFun_invol]

def revAt (N : ℕ) : Function.Embedding ℕ ℕ where
  toFun i := ite (i ≤ N) (N - i) i
  inj' := revAtFun_inj
