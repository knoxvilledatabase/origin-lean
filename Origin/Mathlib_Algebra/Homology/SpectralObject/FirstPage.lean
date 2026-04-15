/-
Extracted from Algebra/Homology/SpectralObject/FirstPage.lean
Genuine: 2 of 5 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# The first page of the spectral sequence of a spectral object

Let `ι` be a preordered type, `X` a spectral object in an abelian
category indexed by `ι`. Let `data : SpectralSequenceDataCore ι c r₀`.
Assume that `X.HasSpectralSequence data` holds. In this file,
we introduce a property `data.HasFirstPageComputation` which allows
to "compute" the objects of the `r₀`th page of the spectral
sequence attached to `X` in terms of objects of the form `X.H`,
and we compute the differential on the first page in terms of `X.δ`,
see `spectralSequence_first_page_d_eq`.

-/

namespace CategoryTheory

open Category ComposableArrows

namespace Abelian

namespace SpectralObject

variable {C ι κ : Type*} [Category C] [Abelian C] [Preorder ι]
  (X : SpectralObject C ι)
  {c : ℤ → ComplexShape κ} {r₀ : ℤ}
  (data : SpectralSequenceDataCore ι c r₀)

namespace SpectralSequenceDataCore

class HasFirstPageComputation : Prop where
  hi₀₁ (pq : κ) : data.i₀ r₀ pq = data.i₁ pq
  hi₂₃ (pq : κ) : data.i₂ pq = data.i₃ r₀ pq

export HasFirstPageComputation (hi₀₁ hi₂₃)

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

end SpectralSequenceDataCore

variable [data.HasFirstPageComputation] [X.HasSpectralSequence data]

noncomputable def spectralSequenceFirstPageXIso (pq : κ)
    (i₁ i₂ : ι) (hi₁ : i₁ = data.i₁ pq) (hi₂ : i₂ = data.i₂ pq)
    (n : ℤ) (hn : n = data.deg pq) :
    ((X.spectralSequence data).page r₀).X pq ≅
      (X.H n).obj (mk₁ (homOfLE (data.le₁₂' pq hi₁ hi₂))) :=
  X.spectralSequencePageXIso data _ (by rfl) _ _ _ _ _
    (by rw [hi₁, ← data.hi₀₁]) hi₁ hi₂ (by rw [hi₂, data.hi₂₃]) _ _ _ hn ≪≫
      X.EIsoH (homOfLE _) (n - 1) n (n + 1)
