/-
Extracted from Algebra/Homology/SpectralObject/HasSpectralSequence.lean
Genuine: 8 of 8 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Shapes of spectral sequences obtained from a spectral object

This file prepares for the construction of the spectral sequence
of a spectral object in an abelian category which shall be conducted
in the file `Mathlib/Algebra/Homology/SpectralObject/SpectralSequence.lean`.

In this file, we introduce a structure `SpectralSequenceDataCore` which
contains a recipe for the construction of the pages of the spectral sequence.
For example, from a spectral object `X` indexed by `EInt` the definition
`coreE₂Cohomological` will allow to construct an `E₂` cohomological
spectral sequence such that the object on position `(p, q)` on the `r`th
page is `E^{p + q}(q - r + 2 ≤ q ≤ q + 1 ≤ q + r - 1)`.
The data (and properties) in the structure `SpectralSequenceDataCore` allow
to define the pages and the differentials directly from the `SpectralObject`
API from the files
`Mathlib/Algebra/Homology/SpectralObject/Page.lean` and
`Mathlib/Algebra/Homology/SpectralObject/Differentials.lean`.
However, the computation of the homology of the differentials in
`Mathlib/Algebra/Homology/SpectralObject/Homology.lean` may not directly
apply: we introduce a typeclass `HasSpectralSequence` which puts
additional conditions on the spectral object so that the homology of a
page identifies to the next page. These conditions are automatically
satisfied for `coreE₂Cohomological`, but this design allows
to obtain a spectral sequence with objects of the pages indexed
by `ℕ × ℕ` instead of `ℤ × ℤ` when suitable conditions are satisfied by
a spectral object indexed by `EInt` (see `coreE₂CohomologicalNat`
and the typeclass `IsFirstQuadrant`).

-/

namespace CategoryTheory

open Category Limits ComposableArrows

namespace Abelian

namespace SpectralObject

variable {C ι κ : Type*} [Category* C] [Abelian C] [Preorder ι]
  {c : ℤ → ComplexShape κ} {r₀ : ℤ}

variable (ι c r₀) in

structure SpectralSequenceDataCore where
  /-- The cohomological degree of objects in the pages -/
  deg : κ → ℤ
  /-- The zeroth index -/
  i₀ (r : ℤ) (pq : κ) (hr : r₀ ≤ r := by lia) : ι
  /-- The first index -/
  i₁ (pq : κ) : ι
  /-- The second index -/
  i₂ (pq : κ) : ι
  /-- The third index -/
  i₃ (r : ℤ) (pq : κ) (hr : r₀ ≤ r := by lia) : ι
  le₀₁ (r : ℤ) (pq : κ) (hr : r₀ ≤ r := by lia) : i₀ r pq ≤ i₁ pq
  le₁₂ (pq : κ) : i₁ pq ≤ i₂ pq
  le₂₃ (r : ℤ) (pq : κ) (hr : r₀ ≤ r := by lia) : i₂ pq ≤ i₃ r pq
  hc (r : ℤ) (pq pq' : κ) (hpq : (c r).Rel pq pq') (hr : r₀ ≤ r := by lia) : deg pq + 1 = deg pq'
  hc₀₂ (r : ℤ) (pq pq' : κ) (hpq : (c r).Rel pq pq') (hr : r₀ ≤ r := by lia) : i₀ r pq = i₂ pq'
  hc₁₃ (r : ℤ) (pq pq' : κ) (hpq : (c r).Rel pq pq') (hr : r₀ ≤ r := by lia) : i₁ pq = i₃ r pq'
  antitone_i₀ (r r' : ℤ) (pq : κ) (hr : r₀ ≤ r := by lia) (hrr' : r ≤ r' := by lia) :
      i₀ r' pq ≤ i₀ r pq
  monotone_i₃ (r r' : ℤ) (pq : κ) (hr : r₀ ≤ r := by lia) (hrr' : r ≤ r' := by lia) :
      i₃ r pq ≤ i₃ r' pq
  i₀_prev (r r' : ℤ) (pq pq' : κ) (hpq : (c r).Rel pq pq') (hrr' : r + 1 = r' := by lia)
      (hr : r₀ ≤ r := by lia) :
      i₀ r' pq = i₁ pq'
  i₃_next (r r' : ℤ) (pq pq' : κ) (hpq : (c r).Rel pq pq') (hrr' : r + 1 = r' := by lia)
      (hr : r₀ ≤ r := by lia) :
      i₃ r' pq' = i₂ pq

namespace SpectralSequenceDataCore

variable (data : SpectralSequenceDataCore ι c r₀)

lemma i₀_le (r r' : ℤ) (pq : κ) (hrr' : r + 1 = r' := by lia) (hr : r₀ ≤ r := by lia) :
    data.i₀ r' pq ≤ data.i₀ r pq :=
  data.antitone_i₀ r r' pq

lemma i₃_le (r r' : ℤ) (pq : κ) (hrr' : r + 1 = r' := by lia) (hr : r₀ ≤ r := by lia) :
    data.i₃ r pq ≤ data.i₃ r' pq :=
  data.monotone_i₃ r r' pq

lemma i₀_le' {r r' : ℤ} (hrr' : r + 1 = r') (hr : r₀ ≤ r) (pq' : κ)
    {i₀' i₀ : ι} (hi₀' : i₀' = data.i₀ r' pq') (hi₀ : i₀ = data.i₀ r pq') :
    i₀' ≤ i₀ := by
  rw [hi₀', hi₀]
  exact data.antitone_i₀ r r' pq'

lemma le₀₁' (r : ℤ) (hr : r₀ ≤ r) (pq' : κ) {i₀ i₁ : ι}
    (hi₀ : i₀ = data.i₀ r pq')
    (hi₁ : i₁ = data.i₁ pq') :
    i₀ ≤ i₁ := by
  have := data.le₀₁ r pq'
  simpa only [hi₀, hi₁] using data.le₀₁ r pq'

lemma le₁₂' (pq' : κ) {i₁ i₂ : ι} (hi₁ : i₁ = data.i₁ pq') (hi₂ : i₂ = data.i₂ pq') :
    i₁ ≤ i₂ := by
  simpa only [hi₁, hi₂] using data.le₁₂ pq'

lemma le₂₃' (r : ℤ) (hr : r₀ ≤ r) (pq' : κ)
    {i₂ i₃ : ι}
    (hi₂ : i₂ = data.i₂ pq')
    (hi₃ : i₃ = data.i₃ r pq') :
    i₂ ≤ i₃ := by
  simpa only [hi₂, hi₃] using data.le₂₃ r pq'

lemma le₃₃' {r r' : ℤ} (hrr' : r + 1 = r') (hr : r₀ ≤ r) (pq' : κ)
    {i₃ i₃' : ι}
    (hi₃ : i₃ = data.i₃ r pq')
    (hi₃' : i₃' = data.i₃ r' pq') :
    i₃ ≤ i₃' := by
  simpa only [hi₃, hi₃'] using data.monotone_i₃ r r' pq'

end SpectralSequenceDataCore
