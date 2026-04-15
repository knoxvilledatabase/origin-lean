/-
Extracted from RingTheory/Extension/Cotangent/Basic.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Naive cotangent complex associated to a presentation.

Given a presentation `0 → I → R[x₁,...,xₙ] → S → 0` (or equivalently a closed embedding `S ↪ Aⁿ`
defined by `I`), we may define the (naive) cotangent complex `I/I² → ⨁ᵢ S dxᵢ → Ω[S/R] → 0`.

## Main results
- `Algebra.Extension.Cotangent`: The conormal space `I/I²`. (Defined in `Generators/Basic`)
- `Algebra.Extension.CotangentSpace`: The cotangent space `⨁ᵢ S dxᵢ`.
- `Algebra.Generators.cotangentSpaceBasis`: The canonical basis on `⨁ᵢ S dxᵢ`.
- `Algebra.Extension.CotangentComplex`: The map `I/I² → ⨁ᵢ S dxᵢ`.
- `Algebra.Extension.toKaehler`: The projection `⨁ᵢ S dxᵢ → Ω[S/R]`.
- `Algebra.Extension.toKaehler_surjective`: The map `⨁ᵢ S dxᵢ → Ω[S/R]` is surjective.
- `Algebra.Extension.exact_cotangentComplex_toKaehler`: `I/I² → ⨁ᵢ S dxᵢ → Ω[S/R]` is exact.
- `Algebra.Extension.Hom.Sub`: If `f` and `g` are two maps between presentations, `f - g` induces
  a map `⨁ᵢ S dxᵢ → I/I²` that makes `f` and `g` homotopic.
- `Algebra.Extension.H1Cotangent`: The first homology of the (naive) cotangent complex
  of `S` over `R`, induced by a given presentation.
- `Algebra.H1Cotangent`: `H¹(L_{S/R})`,
  the first homology of the (naive) cotangent complex of `S` over `R`.

## Implementation detail
We actually develop these material for general extensions (i.e. surjection `P → S`) so that we can
apply them to infinitesimal smooth (or versal) extensions later.

-/

open KaehlerDifferential Module MvPolynomial TensorProduct

namespace Algebra

universe w u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

namespace Extension

variable (P : Extension.{w} R S)

abbrev CotangentSpace : Type _ := S ⊗[P.Ring] Ω[P.Ring⁄R]

noncomputable

def cotangentComplex : P.Cotangent →ₗ[S] P.CotangentSpace :=
  letI f : P.Cotangent ≃ₗ[P.Ring] P.ker.Cotangent :=
    { __ := AddEquiv.refl _, map_smul' := Cotangent.val_smul' }
  (kerCotangentToTensor R P.Ring S ∘ₗ f).extendScalarsOfSurjective P.algebraMap_surjective
