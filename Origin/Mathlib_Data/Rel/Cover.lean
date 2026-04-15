/-
Extracted from Data/Rel/Cover.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Covers in a uniform space

This file defines covers, aka nets, which are a quantitative notion of compactness given an
entourage.

A `U`-cover of a set `s` is a set `N` such that every element of `s` is `U`-close to some element of
`N`.

The concept of uniform covers is used to define two further notions of covering:
* Metric covers: `Metric.IsCover`, defined using the distance entourage.
* Dynamical covers: `Dynamics.IsDynCoverOf`, defined using the dynamical entourage.

## References

[R. Vershynin, *High Dimensional Probability*][vershynin2018high], Section 4.2.
-/

open Set

namespace SetRel

variable {X : Type*} {U V : SetRel X X} {s t N N₁ N₂ : Set X} {x : X}

def IsCover (U : SetRel X X) (s N : Set X) : Prop := ∀ ⦃x⦄, x ∈ s → ∃ y ∈ N, x ~[U] y
