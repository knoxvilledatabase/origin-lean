/-
Extracted from Combinatorics/Quiver/Path/Vertices.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Path Vertices

This file provides lemmas for reasoning about the vertices of a path.
-/

namespace Quiver.Path

open List

variable {V : Type*} [Quiver V]

def «end» {a : V} : ∀ {b : V}, Path a b → V
  | b, _ => b
