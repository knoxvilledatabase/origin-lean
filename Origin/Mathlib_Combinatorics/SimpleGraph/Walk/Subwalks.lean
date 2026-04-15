/-
Extracted from Combinatorics/SimpleGraph/Walk/Subwalks.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Subwalks

We define a relation on walks stating that one walk is the subwalk of another.

## Main definitions

* `SimpleGraph.Walk.IsSubwalk`: A relation on walks stating that the first walk is a contiguous
  subwalk of the second walk.

## Tags
walks, subwalks
-/

namespace SimpleGraph

namespace Walk

variable {V : Type*} {G G' : SimpleGraph V} {u v u' v' : V}

def IsSubwalk {u₁ v₁ u₂ v₂} (p : G.Walk u₁ v₁) (q : G.Walk u₂ v₂) : Prop :=
  ∃ (ru : G.Walk u₂ u₁) (rv : G.Walk v₁ v₂), q = (ru.append p).append rv
