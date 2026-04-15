/-
Extracted from Combinatorics/Quiver/Arborescence.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Arborescences

A quiver `V` is an arborescence (or directed rooted tree) when we have a root vertex `root : V` such
that for every `b : V` there is a unique path from `root` to `b`.

## Main definitions

- `Quiver.Arborescence V`: a typeclass asserting that `V` is an arborescence
- `arborescenceMk`: a convenient way of proving that a quiver is an arborescence
- `RootedConnected r`: a typeclass asserting that there is at least one path from `r` to `b` for
  every `b`.
- `geodesicSubtree r`: given `[RootedConnected r]`, this is a subquiver of `V` which contains
  just enough edges to include a shortest path from `r` to `b` for every `b`.
- `geodesicArborescence : Arborescence (geodesicSubtree r)`: an instance saying that the geodesic
  subtree is an arborescence. This proves the directed analogue of 'every connected graph has a
  spanning tree'. This proof avoids the use of Zorn's lemma.
-/

open Opposite

universe v u

namespace Quiver

class Arborescence (V : Type u) [Quiver.{v} V] : Type max u v where
  /-- The root of the arborescence. -/
  root : V
  /-- There is a unique path from the root to any other vertex. -/
  uniquePath : ∀ b : V, Unique (Path root b)

def root (V : Type u) [Quiver V] [Arborescence V] : V :=
  Arborescence.root

-- INSTANCE (free from Core): {V
