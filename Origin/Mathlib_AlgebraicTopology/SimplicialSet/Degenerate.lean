/-
Extracted from AlgebraicTopology/SimplicialSet/Degenerate.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Degenerate simplices

Given a simplicial set `X` and `n : ℕ`, we define the sets `X.degenerate n`
and `X.nonDegenerate n` of degenerate or non-degenerate simplices of dimension `n`.

Any simplex `x : X _⦋n⦌` can be written in a unique way as `X.map f.op y`
for an epimorphism `f : ⦋n⦌ ⟶ ⦋m⦌` and a non-degenerate `m`-simplex `y`
(see lemmas `exists_nonDegenerate`, `unique_nonDegenerate_dim`,
`unique_nonDegenerate_simplex` and `unique_nonDegenerate_map`).

-/

universe u

open CategoryTheory Simplicial Limits Opposite

namespace SSet

variable (X : SSet.{u})

def degenerate (n : ℕ) : Set (X _⦋n⦌) :=
  setOf (fun x ↦ ∃ (m : ℕ) (_ : m < n) (f : ⦋n⦌ ⟶ ⦋m⦌),
    x ∈ Set.range (X.map f.op))

def nonDegenerate (n : ℕ) : Set (X _⦋n⦌) := (X.degenerate n)ᶜ
