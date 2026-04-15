/-
Extracted from Data/Rel/Separated.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Uniform separation

This file defines a notion of separation of a set relative to a relation.

For a relation `R`, an `R`-separated set `s` is a set such that every pair of elements of `s` is
`R`-unrelated.

The concept of uniformly separated sets is used to define two further notions of separation:
* Metric separation: `Metric.IsSeparated`, defined using the small distance relation.
* Dynamical nets: `Dynamics.IsDynNetIn`, defined using the dynamical relation.

## TODO

* Actually use `SetRel.IsSeparated` to define the above two notions.
* Link to the notion of separation given by pairwise disjoint balls.
-/

open Set

namespace SetRel

variable {X : Type*} {R S : SetRel X X} {s t : Set X} {x : X}

def IsSeparated (R : SetRel X X) (s : Set X) : Prop := s.Pairwise fun x y ↦ ¬ x ~[R] y

protected lemma IsSeparated.empty : IsSeparated R (∅ : Set X) := pairwise_empty _

protected lemma IsSeparated.singleton : IsSeparated R {x} := pairwise_singleton ..
