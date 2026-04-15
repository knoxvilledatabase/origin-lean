/-
Extracted from Analysis/CStarAlgebra/Spectrum.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Spectral properties in C⋆-algebras

In this file, we establish various properties related to the spectrum of elements in C⋆-algebras.
In particular, we show that the spectrum of a unitary element is contained in the unit circle in
`ℂ`, the spectrum of a selfadjoint element is real, the spectral radius of a selfadjoint element
or normal element is its norm, among others.

An essential feature of C⋆-algebras is **spectral permanence**. This is the property that the
spectrum of an element in a closed subalgebra is the same as the spectrum of the element in the
whole algebra. For Banach algebras more generally, and even for Banach ⋆-algebras, this fails.

A consequence of spectral permanence is that one may always enlarge the C⋆-algebra (via a unital
embedding) while preserving the spectrum of any element. In addition, it allows us to make sense of
the spectrum of elements in non-unital C⋆-algebras by considering them as elements in the
`Unitization` of the C⋆-algebra, or indeed *any* unital C⋆-algebra. Of course, one may do this
(that is, consider the spectrum of an element in a non-unital by embedding it in a unital algebra)
for any Banach algebra, but the downside in that setting is that embedding in different unital
algebras results in varying spectra.

In Mathlib, we don't *define* the spectrum of an element in a non-unital C⋆-algebra, and instead
simply consider the `quasispectrum` so as to avoid depending on a choice of unital algebra. However,
we can still establish a form of spectral permanence.

## Main statements

+ `Unitary.spectrum_subset_circle`: The spectrum of a unitary element is contained in the unit
  sphere in `ℂ`.
+ `IsSelfAdjoint.spectralRadius_eq_nnnorm`: The spectral radius of a selfadjoint element is equal
  to its norm.
+ `IsStarNormal.spectralRadius_eq_nnnorm`: The spectral radius of a normal element is equal to
  its norm.
+ `IsSelfAdjoint.mem_spectrum_eq_re`: Any element of the spectrum of a selfadjoint element is real.
* `StarSubalgebra.coe_isUnit`: for `x : S` in a C⋆-Subalgebra `S` of `A`, then `↑x : A` is a Unit
  if and only if `x` is a unit.
* `StarSubalgebra.spectrum_eq`: **spectral permanence** for `x : S`, where `S` is a C⋆-Subalgebra
  of `A`, `spectrum ℂ x = spectrum ℂ (x : A)`.

## TODO

+ prove a variation of spectral permanence using `StarAlgHom` instead of `StarSubalgebra`.
+ prove a variation of spectral permanence for `quasispectrum`.

-/

local notation "σ" => spectrum

local postfix:max "⋆" => star

open scoped Topology ENNReal

open Filter ENNReal spectrum CStarRing NormedSpace

section UnitarySpectrum

variable {𝕜 : Type*} [NormedField 𝕜] {E : Type*} [NormedRing E] [StarRing E] [CStarRing E]
  [NormedAlgebra 𝕜 E] [CompleteSpace E]

theorem Unitary.spectrum_subset_circle (u : unitary E) :
    spectrum 𝕜 (u : E) ⊆ Metric.sphere 0 1 := by
  nontriviality E
  refine fun k hk => mem_sphere_zero_iff_norm.mpr (le_antisymm ?_ ?_)
  · simpa only [CStarRing.norm_coe_unitary u] using norm_le_norm_of_mem hk
  · rw [← Unitary.val_toUnits_apply u] at hk
    have hnk := ne_zero_of_mem_of_unit hk
    rw [← inv_inv (Unitary.toUnits u), ← spectrum.map_inv, Set.mem_inv] at hk
    have : ‖k‖⁻¹ ≤ ‖(↑(Unitary.toUnits u)⁻¹ : E)‖ := by
      simpa only [norm_inv] using norm_le_norm_of_mem hk
    simpa using inv_le_of_inv_le₀ (norm_pos_iff.mpr hnk) this
