/-
Extracted from Data/Finsupp/Antidiagonal.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# The `Finsupp` counterpart of `Multiset.antidiagonal`.

The antidiagonal of `s : α →₀ ℕ` consists of
all pairs `(t₁, t₂) : (α →₀ ℕ) × (α →₀ ℕ)` such that `t₁ + t₂ = s`.
-/

namespace Finsupp

open Finset

universe u

variable {α : Type u} [DecidableEq α]

noncomputable def antidiagonal' (f : α →₀ ℕ) : (α →₀ ℕ) × (α →₀ ℕ) →₀ ℕ :=
  Multiset.toFinsupp
    ((Finsupp.toMultiset f).antidiagonal.map (Prod.map Multiset.toFinsupp Multiset.toFinsupp))

-- INSTANCE (free from Core): instHasAntidiagonal
