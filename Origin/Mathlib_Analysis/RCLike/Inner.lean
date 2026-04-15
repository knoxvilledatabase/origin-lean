/-
Extracted from Analysis/RCLike/Inner.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# L2 inner product of finite sequences

This file defines the weighted L2 inner product of functions `f g : ι → R` where `ι` is a fintype as
`∑ i, conj (f i) * g i`. This convention (conjugation on the left) matches the inner product coming
from `RCLike.innerProductSpace`.

## TODO

* Build a non-instance `InnerProductSpace` from `wInner`.
* `cWeight` is a poor name. Can we find better? It doesn't hugely matter for typing, since it's
  hidden behind the `⟪f, g⟫ₙ_[𝕝]` notation, but it does show up in lemma names
  `⟪f, g⟫_[𝕝, cWeight]` is called `wInner_cWeight`. Maybe we should introduce some naming
  convention, similarly to `MeasureTheory.average`?
-/

open Finset Function Real WithLp

open scoped BigOperators ComplexConjugate ComplexOrder InnerProductSpace

variable {ι κ 𝕜 : Type*} {E : ι → Type*} [Fintype ι]

namespace RCLike

variable [RCLike 𝕜]

section Pi

variable [∀ i, SeminormedAddCommGroup (E i)] [∀ i, InnerProductSpace 𝕜 (E i)] {w : ι → ℝ}

def wInner (w : ι → ℝ) (f g : ∀ i, E i) : 𝕜 := ∑ i, w i • ⟪f i, g i⟫_𝕜

noncomputable abbrev cWeight : ι → ℝ := Function.const _ (Fintype.card ι)⁻¹
