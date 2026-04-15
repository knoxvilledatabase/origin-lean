/-
Extracted from Combinatorics/Quiver/Subquiver.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
## Wide subquivers

A wide subquiver `H` of a quiver `H` consists of a subset of the edge set `a ⟶ b` for
every pair of vertices `a b : V`. We include 'wide' in the name to emphasize that these
subquivers by definition contain all vertices.
-/

universe v u

def WideSubquiver (V) [Quiver.{v} V] :=
  ∀ a b : V, Set (a ⟶ b)
