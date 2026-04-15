/-
Extracted from Algebra/Polynomial/OfFn.lean
Genuine: 2 of 4 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# `Polynomial.ofFn` and `Polynomial.toFn`

In this file we introduce `ofFn` and `toFn`, two functions that associate a polynomial to the vector
of its coefficients and vice versa. We prove some basic APIs for these functions.

## Main definitions

- `Polynomial.toFn n` associates to a polynomial the vector of its first `n` coefficients.
- `Polynomial.ofFn n` associates to a vector of length `n` the polynomial that has the entries of
  the vector as coefficients.
-/

namespace Polynomial

section toFn

variable {R : Type*} [Semiring R]

noncomputable def toFn (n : ℕ) : R[X] →ₗ[R] Fin n → R := LinearMap.pi (fun i ↦ lcoeff R i)

end toFn

section ofFn

variable {R : Type*} [Semiring R] [DecidableEq R]

def ofFn (n : ℕ) : (Fin n → R) →ₗ[R] R[X] where
  toFun v := ⟨(List.ofFn v).toFinsupp⟩
  map_add' x y := by
    ext i
    by_cases h : i < n
    · simp [h]
    · simp [h]
  map_smul' x p := by
    ext i
    by_cases h : i < n
    · simp [h]
    · simp [h]
