/-
Extracted from Combinatorics/Additive/Corner/Roth.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The corners theorem and Roth's theorem

This file proves the corners theorem and Roth's theorem on arithmetic progressions of length three.

## References

* [Yaël Dillies, Bhavik Mehta, *Formalising Szemerédi’s Regularity Lemma in Lean*][srl_itp]
* [Wikipedia, *Corners theorem*](https://en.wikipedia.org/wiki/Corners_theorem)
-/

open Finset SimpleGraph TripartiteFromTriangles

open Function hiding graph

open Fintype (card)

variable {G : Type*} [AddCommGroup G] {A : Finset (G × G)} {a b c : G} {n : ℕ} {ε : ℝ}

namespace Corners

private def triangleIndices (A : Finset (G × G)) : Finset (G × G × G) :=
  A.map ⟨fun (a, b) ↦ (a, b, a + b), by rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ ⟨⟩; rfl⟩
