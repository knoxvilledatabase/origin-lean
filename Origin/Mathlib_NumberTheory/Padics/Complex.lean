/-
Extracted from NumberTheory/Padics/Complex.lean
Genuine: 2 of 7 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-!
# The field `ℂ_[p]` of `p`-adic complex numbers.

In this file we define the field `ℂ_[p]` of `p`-adic complex numbers as the `p`-adic completion of
an algebraic closure of `ℚ_[p]`. We endow `ℂ_[p]` with both a normed field and a valued field
structure, induced by the unique extension of the `p`-adic norm to `ℂ_[p]`.

## Main Definitions
* `PadicAlgCl p` : the algebraic closure of `ℚ_[p]`.
* `PadicComplex p` : the type of `p`-adic complex numbers, denoted by `ℂ_[p]`.
* `PadicComplexInt p` : the ring of integers of `ℂ_[p]`.

## Main Results

* `PadicComplex.norm_extends` : the norm on `ℂ_[p]` extends the norm on `PadicAlgCl p`, and hence
  the norm on `ℚ_[p]`.
* `PadicComplex.isNonarchimedean` : The norm on `ℂ_[p]` is nonarchimedean.
* `PadicComplex.isAlgClosed` : `ℂ_[p]` is algebraically closed.

## Notation

We introduce the notation `ℂ_[p]` for the `p`-adic complex numbers, and `𝓞_ℂ_[p]` for its ring of
integers.

## Tags

p-adic, p adic, padic, norm, valuation, Cauchy, completion, p-adic completion
-/

noncomputable section

open Valuation

open scoped NNReal

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

abbrev PadicAlgCl := AlgebraicClosure ℚ_[p]

namespace PadicAlgCl

-- INSTANCE (free from Core): isAlgebraic

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): normedField

theorem isNonarchimedean : IsNonarchimedean (norm : PadicAlgCl p → ℝ) :=
  isNonarchimedean_spectralNorm (K := ℚ_[p]) (L := PadicAlgCl p)

-- INSTANCE (free from Core): normedAlgebra
