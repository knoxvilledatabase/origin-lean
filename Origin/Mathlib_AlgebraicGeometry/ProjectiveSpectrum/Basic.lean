/-
Extracted from AlgebraicGeometry/ProjectiveSpectrum/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Basic properties of the scheme `Proj A`

The scheme `Proj 𝒜` for a graded ring `𝒜` is constructed in
`Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Scheme.lean`.
In this file we provide basic properties of the scheme.

## Main results
- `AlgebraicGeometry.Proj.toSpecZero`: The structure map `Proj A ⟶ Spec (A 0)`.
- `AlgebraicGeometry.Proj.basicOpenIsoSpec`:
  The canonical isomorphism `Proj A |_ D₊(f) ≅ Spec (A_f)₀`
  when `f` is homogeneous of positive degree.
- `AlgebraicGeometry.Proj.awayι`: The open immersion `Spec (A_f)₀ ⟶ Proj A`.
- `AlgebraicGeometry.Proj.affineOpenCover`: The open cover of `Proj A` by `Spec (A_f)₀` for all
  homogeneous `f` of positive degree.
- `AlgebraicGeometry.Proj.stalkIso`:
  The stalk of `Proj A` at `x` is the degree `0` part of the localization of `A` at `x`.
- `AlgebraicGeometry.Proj.fromOfGlobalSections`:
  Given a map `f : A →+* Γ(X, ⊤)` such that the image of the irrelevant ideal under `f`
  generates the whole ring, we can construct a map `X ⟶ Proj 𝒜`.

-/

namespace AlgebraicGeometry.Proj

open HomogeneousLocalization CategoryTheory

universe u

variable {σ : Type*} {A : Type u}

variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]

variable (𝒜 : ℕ → σ)

variable [GradedRing 𝒜]

section basicOpen

variable (f g : A)

def basicOpen : (Proj 𝒜).Opens :=
  ProjectiveSpectrum.basicOpen 𝒜 f
