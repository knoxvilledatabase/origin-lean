/-
Extracted from AlgebraicGeometry/AffineSpace.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Affine space

## Main definitions

- `AlgebraicGeometry.AffineSpace`: `𝔸(n; S)` is the affine `n`-space over `S`.
- `AlgebraicGeometry.AffineSpace.coord`: The standard coordinate functions on the affine space.
- `AlgebraicGeometry.AffineSpace.homOfVector`:
  The morphism `X ⟶ 𝔸(n; S)` given by a `X ⟶ S` and a choice of `n`-coordinate functions.
- `AlgebraicGeometry.AffineSpace.homOverEquiv`:
  `S`-morphisms into `Spec 𝔸(n; S)` are equivalent to the choice of `n` global sections.
- `AlgebraicGeometry.AffineSpace.SpecIso`: `𝔸(n; Spec R) ≅ Spec R[n]`

-/

open CategoryTheory Limits MvPolynomial

noncomputable section

namespace AlgebraicGeometry

universe v u

variable (n : Type v) (S : Scheme.{max u v})

local notation3 "ℤ[" n "]" => CommRingCat.of (MvPolynomial n (ULift ℤ))

local notation3 "ℤ[" n "].{" u ", " v "}" => CommRingCat.of (MvPolynomial n (ULift.{max u v} ℤ))

def AffineSpace (n : Type v) (S : Scheme.{max u v}) : Scheme.{max u v} :=
  pullback (terminal.from S) (terminal.from (Spec ℤ[n].{u, v}))

namespace AffineSpace

scoped[AlgebraicGeometry] notation "𝔸(" n "; " S ")" => AffineSpace n S

variable {n} in

lemma of_mvPolynomial_int_ext {R} {f g : ℤ[n] ⟶ R} (h : ∀ i, f (.X i) = g (.X i)) : f = g := by
  suffices f.hom.comp (MvPolynomial.mapEquiv _ ULift.ringEquiv.symm).toRingHom =
      g.hom.comp (MvPolynomial.mapEquiv _ ULift.ringEquiv.symm).toRingHom by
    ext x
    · obtain ⟨x⟩ := x
      simpa [-map_intCast, -eq_intCast] using DFunLike.congr_fun this (C x)
    · simpa [-map_intCast, -eq_intCast] using DFunLike.congr_fun this (X x)
  ext1
  · exact RingHom.ext_int _ _
  · simpa using h _
