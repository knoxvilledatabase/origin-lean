/-
Extracted from Combinatorics/Matroid/Rank/Finite.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Finite-rank sets

`Matroid.IsRkFinite M X`  means that every basis of the set `X` in the matroid `M` is finite,
or equivalently that the restriction of `M` to `X` is `Matroid.RankFinite`.
Sets in a matroid with `IsRkFinite` are the largest class of sets for which one can do nontrivial
integer arithmetic involving the rank function.

## Implementation Details

Unlike most set predicates on matroids, a set `X` with `M.IsRkFinite X` need not satisfy `X ⊆ M.E`,
so may contain junk elements. This seems to be what makes the definition easiest to use.
-/

variable {α : Type*} {M : Matroid α} {X Y I : Set α} {e : α}

open Set

namespace Matroid

def IsRkFinite (M : Matroid α) (X : Set α) : Prop := (M ↾ X).RankFinite

lemma IsRkFinite.rankFinite (hX : M.IsRkFinite X) : (M ↾ X).RankFinite :=
  hX
