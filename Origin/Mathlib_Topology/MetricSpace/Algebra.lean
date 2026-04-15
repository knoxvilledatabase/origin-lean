/-
Extracted from Topology/MetricSpace/Algebra.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Compatibility of algebraic operations with metric space structures

In this file we define mixin typeclasses `LipschitzMul`, `LipschitzAdd`,
`IsBoundedSMul` expressing compatibility of multiplication, addition and scalar-multiplication
operations with an underlying metric space structure.  The intended use case is to abstract certain
properties shared by normed groups and by `R≥0`.

## Implementation notes

We deduce a `ContinuousMul` instance from `LipschitzMul`, etc.  In principle there should
be an intermediate typeclass for uniform spaces, but the algebraic hierarchy there (see
`IsUniformGroup`) is structured differently.

-/

open NNReal Filter Set

open scoped Topology Uniformity

noncomputable section

variable (α β : Type*) [PseudoMetricSpace α] [PseudoMetricSpace β]

section LipschitzMul

class LipschitzAdd [AddMonoid β] : Prop where
  lipschitz_add : ∃ C, LipschitzWith C fun p : β × β => p.1 + p.2
