/-
Extracted from Combinatorics/Additive/Randomisation.lean
Genuine: 1 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Combinatorics.Additive.Dissociation

noncomputable section

/-!
# Randomising by a function of dissociated support

This file proves that a function from a finite abelian group can be randomised by a function of
dissociated support.

Precisely, for `G` a finite abelian group and two functions `c : AddChar G ℂ → ℝ` and
`d : AddChar G ℂ → ℝ` such that `{ψ | d ψ ≠ 0}` is dissociated, the product of the `c ψ` over `ψ` is
the same as the average over `a` of the product of the `c ψ + Re (d ψ * ψ a)`.
-/

open Finset

open scoped BigOperators ComplexConjugate

variable {G : Type*} [Fintype G] [AddCommGroup G] {p : ℕ}
