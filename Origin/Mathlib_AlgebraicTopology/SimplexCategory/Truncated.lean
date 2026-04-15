/-
Extracted from AlgebraicTopology/SimplexCategory/Truncated.lean
Genuine: 4 of 7 | Dissolved: 1 | Infrastructure: 2
-/
import Origin.Core

/-! # Properties of the truncated simplex category

We prove that for `n > 0`, the inclusion functor from the `n`-truncated simplex category to the
untruncated simplex category, and the inclusion functor from the `n`-truncated to the `m`-truncated
simplex category, for `n ≤ m` are initial.
-/

open Simplicial CategoryTheory

namespace SimplexCategory.Truncated

-- INSTANCE (free from Core): {d

-- INSTANCE (free from Core): initial_inclusion

-- DISSOLVED: initial_incl

abbrev δ (m : Nat) {n} (i : Fin (n + 2)) (hn := by decide) (hn' := by decide) :
  (⟨⦋n⦌, hn⟩ : SimplexCategory.Truncated m) ⟶ ⟨⦋n + 1⦌, hn'⟩ := Hom.tr (SimplexCategory.δ i)

abbrev σ (m : Nat) {n} (i : Fin (n + 1)) (hn := by decide) (hn' := by decide) :
    (⟨⦋n + 1⦌, hn⟩ : SimplexCategory.Truncated m) ⟶ ⟨⦋n⦌, hn'⟩ := Hom.tr (SimplexCategory.σ i)

section Two

abbrev δ₂ {n} (i : Fin (n + 2)) (hn := by decide) (hn' := by decide) := δ 2 i hn hn'

abbrev σ₂ {n} (i : Fin (n + 1)) (hn := by decide) (hn' := by decide) := σ 2 i hn hn'
