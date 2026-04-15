/-
Extracted from Analysis/Convex/BetweenList.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Betweenness for lists of points.

This file defines notions of lists of points in an affine space being in order on a line.

## Main definitions

* `List.Wbtw R l`: The points in list `l` are weakly in order on a line.
* `List.Sbtw R l`: The points in list `l` are strictly in order on a line.

-/

variable (R : Type*) {V V' P P' : Type*}

open AffineEquiv AffineMap

namespace List

section OrderedRing

variable [Ring R] [PartialOrder R] [AddCommGroup V] [Module R V] [AddTorsor V P]

variable [AddCommGroup V'] [Module R V'] [AddTorsor V' P']

protected def Wbtw (l : List P) : Prop :=
  l.Triplewise (Wbtw R)

variable {R}

lemma wbtw_cons {p : P} {l : List P} : (p :: l).Wbtw R ↔ l.Pairwise (Wbtw R p) ∧ l.Wbtw R :=
  triplewise_cons

variable (R)

protected def Sbtw (l : List P) : Prop :=
  l.Wbtw R ∧ l.Pairwise (· ≠ ·)

variable (P)
