/-
Extracted from Algebra/Homology/SpectralObject/SpectralSequence.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The spectral sequence of a spectral object

The main definition in this file is `Abelian.SpectralObject.spectralSequence`.
Assume that `X` is a spectral object indexed by `ι` in an abelian category `C`,
and that we have `data : SpectralSequenceDataCore ι c r₀` for a family
of complex shapes `c : ℤ → ComplexShape κ` for a type `κ` and `r₀ : ℤ`.
Then, under the assumption `X.HasSpectralSequence data` (see the file
`Mathlib/Algebra/Homology/SpectralObject/HasSpectralSequence.lean`),
we obtain `X.spectralSequence data` which is a spectral sequence starting
on page `r₀`, such that the `r`th page (for `r₀ ≤ r`) is a homological
complex of shape `c r`.

## Outline of the construction

The construction of the spectral sequence is as follows. If `r₀ ≤ r`
and `pq : κ`, we define the object of the spectral sequence in position `pq`
on the `r`th page as `E^d(i₀ r pq ≤ i₁ pq ≤ i₂ pq ≤ i₃ r pq)`
where `d := data.deg pq` and the indices `i₀`, `i₁`, `i₂`, `i₃` are given
by `data` (they all depend on `pq`, and `i₀` and `i₃` also depend on the page `r`),
see `spectralSequencePageXIso`.

When `(c r).Rel pq pq'`, the differential from the object in position `pq`
to the object in position `pq'` on the `r`th page can be related to
the differential `X.d` of the spectral object (see the lemma
`spectralSequence_page_d_eq`). Indeed, the assumptions that
are part of `data` give equalities of indices `i₂ r pq' = i₀ r pq`
and `i₃ pq' = i₁ pq`, so that we have a chain of inequalities
`i₀ r pq' ≤ i₁ pq' ≤ i₂ pq' ≤ i₃ r pq' ≤ i₂ pq ≤ i₃ r pq` for which
the API of spectral objects provides a differential
`X.d : E^n(i₀ r pq ≤ i₁ pq ≤ i₂ pq ≤ i₃ r pq) ⟶ E^{n + 1}(i₀ r pq' ≤ i₁ pq' ≤ i₂ pq' ≤ i₃ r pq')`.

Now, fix `r` and three positions `pq`, `pq'` and `pq''` such that
`pq` is the previous object of `pq'` for `c r` and `pq''` is the next
object of `pq'`. (Note that in case there are no nontrivial differentials
to the object `pq'` for the complex shape `c r`, according to the homological
complex API, we have `pq = pq'` and the differential is zero. Similarly,
when there are no nontrivial differentials from the object in position `pq'`,
we have `pq'' = pq` and the corresponding differential is zero.)
In the favourable case where both `(c r).Rel pq pq'` and `(c r).Rel pq' pq''`
hold, the definition `SpectralObject.SpectralSequence.shortComplexIso`
in this file can be used in combination to `SpectralObject.SpectralSequence.dHomologyIso`
in order to compute the homology of the differentials.)

In the general case, using the assumptions in `X.HasSpectralSequence data`,
we provide a limit kernel fork `kf` and
a limit cokernel cofork `cc` of the differentials on the `r`th page,
together with an epi-mono factorization `fac` which allows
to obtain that the homology of the `r`th page identifies to the next page (see the definitions
`SpectralObject.SpectralSequence.homologyData` and
`SpectralObject.spectralSequenceHomologyData`).

## Spectral objects indexed by `EInt`.

When `X` is a spectral object indexed by the extended integers `EInt`,
we obtain the `E₂`-cohomological spectral sequence
`X.E₂SpectralSequence` where the objects of each page are indexed by
`ℤ × ℤ` (the condition `HasSpectralSequence` is automatically satisfied).
Under the `X.IsFirstQuadrant` assumption, we obtain
`X.E₂SpectralSequenceNat` which is a first quadrant `E₂`-spectral
sequence (the objects in the pages are indexed by `ℕ × ℕ` instead
of `ℤ × ℤ`).

-/

namespace CategoryTheory

open Limits ComposableArrows

namespace Abelian

namespace SpectralObject

variable {C ι κ : Type*} [Category* C] [Abelian C] [Preorder ι]
  (X : SpectralObject C ι)
  {c : ℤ → ComplexShape κ} {r₀ : ℤ}

variable (data : SpectralSequenceDataCore ι c r₀)

namespace SpectralSequence

noncomputable def pageX (r : ℤ) (pq : κ) (hr : r₀ ≤ r := by lia) : C :=
  X.E (homOfLE (data.le₀₁ r pq)) (homOfLE (data.le₁₂ pq)) (homOfLE (data.le₂₃ r pq))
    (data.deg pq - 1) (data.deg pq) (data.deg pq + 1)

noncomputable def pageXIso (r : ℤ) (hr : r₀ ≤ r) (pq : κ)
    (i₀ i₁ i₂ i₃ : ι) (h₀ : i₀ = data.i₀ r pq) (h₁ : i₁ = data.i₁ pq)
    (h₂ : i₂ = data.i₂ pq) (h₃ : i₃ = data.i₃ r pq)
    (n₀ n₁ n₂ : ℤ) (h : n₁ = data.deg pq)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    pageX X data r pq hr ≅ X.E
      (homOfLE (data.le₀₁' r hr pq h₀ h₁))
      (homOfLE (data.le₁₂' pq h₁ h₂))
      (homOfLE (data.le₂₃' r hr pq h₂ h₃))
      n₀ n₁ n₂ hn₁ hn₂ :=
  eqToIso (by
    obtain rfl : n₀ = n₁ - 1 := by lia
    subst h hn₂ h₀ h₁ h₂ h₃
    rfl)

open Classical in

noncomputable def pageD (r : ℤ) (pq pq' : κ) (hr : r₀ ≤ r := by lia) :
    pageX X data r pq hr ⟶ pageX X data r pq' hr :=
  if hpq : (c r).Rel pq pq'
    then
      X.d (homOfLE (data.le₀₁ r pq'))
        (homOfLE (data.le₁₂' pq' rfl (data.hc₀₂ r pq pq' hpq)))
        (homOfLE (data.le₀₁ r pq)) (homOfLE (data.le₁₂ pq)) (homOfLE (data.le₂₃ r pq))
        (data.deg pq - 1) (data.deg pq) (data.deg pq + 1) (data.deg pq + 2) ≫
      (pageXIso _ _ _ _ _ _ _ _ _ rfl rfl
        (data.hc₀₂ r pq pq' hpq) (data.hc₁₃ r pq pq' hpq) _ _ _ (data.hc r pq pq' hpq) rfl _).inv
    else 0

set_option backward.isDefEq.respectTransparency false in

lemma pageD_eq (r : ℤ) (hr : r₀ ≤ r) (pq pq' : κ) (hpq : (c r).Rel pq pq')
    {i₀ i₁ i₂ i₃ i₄ i₅ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
    (f₄ : i₃ ⟶ i₄) (f₅ : i₄ ⟶ i₅)
    (h₀ : i₀ = data.i₀ r pq') (h₁ : i₁ = data.i₁ pq') (h₂ : i₂ = data.i₀ r pq)
    (h₃ : i₃ = data.i₁ pq) (h₄ : i₄ = data.i₂ pq) (h₅ : i₅ = data.i₃ r pq)
    (n₀ n₁ n₂ n₃ : ℤ) (hn₁' : n₁ = data.deg pq)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) (hn₃ : n₂ + 1 = n₃ := by lia) :
    pageD X data r pq pq' =
      (pageXIso _ _ _ _ _ _ _ _ _ h₂ h₃ h₄ h₅ _ _ _ hn₁' _ _).hom ≫
        X.d f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ ≫
        (pageXIso _ _ _ _ _ _ _ _ _ h₀ h₁ (by rw [h₂, data.hc₀₂ r pq pq' hpq])
          (by rw [h₃, data.hc₁₃ r pq pq' hpq]) _ _ _
          (by simpa only [← hn₂, hn₁'] using data.hc r pq pq' hpq) _ _).inv := by
  subst hn₁' h₀ h₁ h₂ h₃ h₄ h₅
  obtain rfl : n₀ = data.deg pq - 1 := by lia
  obtain rfl : n₂ = data.deg pq + 1 := by lia
  obtain rfl : n₃ = data.deg pq + 2 := by lia
  dsimp [pageD, pageXIso]
  rw [dif_pos hpq, Category.id_comp]
  rfl
