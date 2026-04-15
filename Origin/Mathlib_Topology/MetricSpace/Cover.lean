/-
Extracted from Topology/MetricSpace/Cover.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Covers in a metric space

This file defines covers, aka nets, which are a quantitative notion of compactness in a metric
space.

A `ε`-cover of a set `s` is a set `N` such that every element of `s` is at distance at most `ε` to
some element of `N`.

In a proper metric space, sets admitting a finite cover are precisely the relatively compact sets.

## References

[R. Vershynin, *High Dimensional Probability*][vershynin2018high], Section 4.2.
-/

open Set

open scoped NNReal

namespace Metric

variable {X Y : Type*}

section PseudoEMetricSpace

variable [PseudoEMetricSpace X] [PseudoEMetricSpace Y] {ε δ : ℝ≥0} {s t N N₁ N₂ : Set X} {x : X}

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

def IsCover (ε : ℝ≥0) (s N : Set X) : Prop := SetRel.IsCover {(x, y) | edist x y ≤ ε} s N
