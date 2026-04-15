/-
Extracted from Algebra/Polynomial/Eval/Defs.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Evaluating a polynomial

## Main definitions
* `Polynomial.eval₂`: evaluate `p : R[X]` in `S` given a ring hom `f : R →+* S` and `x : S`.
* `Polynomial.eval`: evaluate `p : R[X]` given `x : R`.
* `Polynomial.IsRoot`: `x : R` is a root of `p : R[X]`.
* `Polynomial.comp`: compose two polynomials `p q : R[X]` by evaluating `p` at `q`.
* `Polynomial.map`: apply `f : R →+* S` to the coefficients of `p : R[X]`.

We also provide the following bundled versions:
* `Polynomial.eval₂AddMonoidHom`, `Polynomial.eval₂RingHom`
* `Polynomial.evalRingHom`
* `Polynomial.compRingHom`
* `Polynomial.mapRingHom`

We include results on applying the definitions to `C`, `X` and ring operations.

-/

noncomputable section

open Finset AddMonoidAlgebra

open Polynomial

namespace Polynomial

universe u v w y

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

section Semiring

variable [Semiring R] {p q r : R[X]}

variable [Semiring S]

variable (f : R →+* S) (x : S)

irreducible_def eval₂ (p : R[X]) : S :=
  p.sum fun e a => f a * x ^ e

theorem eval₂_eq_sum {f : R →+* S} {x : S} : p.eval₂ f x = p.sum fun e a => f a * x ^ e := by
  rw [eval₂_def]

theorem eval₂_congr {R S : Type*} [Semiring R] [Semiring S] {f g : R →+* S} {s t : S}
    {φ ψ : R[X]} : f = g → s = t → φ = ψ → eval₂ f s φ = eval₂ g t ψ := by
  rintro rfl rfl rfl; rfl
