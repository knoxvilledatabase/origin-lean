/-
Extracted from AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean
Genuine: 8 of 9 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Division polynomials of Weierstrass curves

This file defines certain polynomials associated to division polynomials of Weierstrass curves.
These are defined in terms of the auxiliary sequences for normalised elliptic divisibility sequences
(EDS) as defined in `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`.

## Mathematical background

Let `W` be a Weierstrass curve over a commutative ring `R`. The sequence of `n`-division polynomials
`ψₙ ∈ R[X, Y]` of `W` is the normalised EDS with initial values
* `ψ₀ := 0`,
* `ψ₁ := 1`,
* `ψ₂ := 2Y + a₁X + a₃`,
* `ψ₃ := 3X⁴ + b₂X³ + 3b₄X² + 3b₆X + b₈`, and
* `ψ₄ := ψ₂ ⬝ (2X⁶ + b₂X⁵ + 5b₄X⁴ + 10b₆X³ + 10b₈X² + (b₂b₈ - b₄b₆)X + (b₄b₈ - b₆²))`.

Furthermore, define the associated sequences `φₙ, ωₙ ∈ R[X, Y]` by
* `φₙ := Xψₙ² - ψₙ₊₁ ⬝ ψₙ₋₁`, and
* `ωₙ := (ψ₂ₙ / ψₙ - ψₙ ⬝ (a₁φₙ + a₃ψₙ²)) / 2`.

Note that `ωₙ` is always well-defined as a polynomial in `R[X, Y]`. As a start, it can be shown by
induction that `ψₙ` always divides `ψ₂ₙ` in `R[X, Y]`, so that `ψ₂ₙ / ψₙ` is always well-defined as
a polynomial, while division by `2` is well-defined when `R` has characteristic different from `2`.
In general, it can be shown that `2` always divides the polynomial `ψ₂ₙ / ψₙ - ψₙ ⬝ (a₁φₙ + a₃ψₙ²)`
in the characteristic `0` universal ring `𝓡[X, Y] := ℤ[A₁, A₂, A₃, A₄, A₆][X, Y]` of `W`, where the
`Aᵢ` are indeterminates. Then `ωₙ` can be equivalently defined as the image of this division under
the associated universal morphism `𝓡[X, Y] → R[X, Y]` mapping `Aᵢ` to `aᵢ`.

Now, in the coordinate ring `R[W]`, note that `ψ₂²` is congruent to the polynomial
`Ψ₂Sq := 4X³ + b₂X² + 2b₄X + b₆ ∈ R[X]`. As such, the recurrences of a normalised EDS show that
`ψₙ / ψ₂` are congruent to certain polynomials in `R[W]`. In particular, define `preΨₙ ∈ R[X]` as
the auxiliary sequence for a normalised EDS with extra parameter `Ψ₂Sq²` and initial values
* `preΨ₀ := 0`,
* `preΨ₁ := 1`,
* `preΨ₂ := 1`,
* `preΨ₃ := ψ₃`, and
* `preΨ₄ := ψ₄ / ψ₂`.

The corresponding normalised EDS `Ψₙ ∈ R[X, Y]` is then given by
* `Ψₙ := preΨₙ ⬝ ψ₂` if `n` is even, and
* `Ψₙ := preΨₙ` if `n` is odd.

Furthermore, define the associated sequences `ΨSqₙ, Φₙ ∈ R[X]` by
* `ΨSqₙ := preΨₙ² ⬝ Ψ₂Sq` if `n` is even,
* `ΨSqₙ := preΨₙ²` if `n` is odd,
* `Φₙ := XΨSqₙ - preΨₙ₊₁ ⬝ preΨₙ₋₁` if `n` is even, and
* `Φₙ := XΨSqₙ - preΨₙ₊₁ ⬝ preΨₙ₋₁ ⬝ Ψ₂Sq` if `n` is odd.

With these definitions, `ψₙ ∈ R[X, Y]` and `φₙ ∈ R[X, Y]` are congruent in `R[W]` to `Ψₙ ∈ R[X, Y]`
and `Φₙ ∈ R[X]` respectively, which are defined in terms of `Ψ₂Sq ∈ R[X]` and `preΨₙ ∈ R[X]`.

## Main definitions

* `WeierstrassCurve.preΨ`: the univariate polynomials `preΨₙ`.
* `WeierstrassCurve.ΨSq`: the univariate polynomials `ΨSqₙ`.
* `WeierstrassCurve.Ψ`: the bivariate polynomials `Ψₙ`.
* `WeierstrassCurve.Φ`: the univariate polynomials `Φₙ`.
* `WeierstrassCurve.ψ`: the bivariate `n`-division polynomials `ψₙ`.
* `WeierstrassCurve.φ`: the bivariate polynomials `φₙ`.
* TODO: the bivariate polynomials `ωₙ`.

## Implementation notes

Analogously to `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`, the bivariate polynomials
`Ψₙ` are defined in terms of the univariate polynomials `preΨₙ`. This is done partially to avoid
ring division, but more crucially to allow the definition of `ΨSqₙ` and `Φₙ` as univariate
polynomials without needing to work under the coordinate ring, and to allow the computation of their
leading terms without ambiguity. Furthermore, evaluating these polynomials at a rational point on
`W` recovers their original definition up to linear combinations of the Weierstrass equation of `W`,
hence also avoiding the need to work in the coordinate ring.

TODO: implementation notes for the definition of `ωₙ`.

## References

[J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, division polynomial, torsion point
-/

open Polynomial

open scoped Polynomial.Bivariate

local macro "C_simp" : tactic =>

  `(tactic| simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow])

universe r s u v

namespace WeierstrassCurve

variable {R : Type r} {S : Type s} [CommRing R] [CommRing S] (W : WeierstrassCurve R)

section Ψ₂Sq

/-! ### The univariate polynomial `Ψ₂Sq` -/

noncomputable def ψ₂ : R[X][Y] :=
  W.toAffine.polynomialY

noncomputable def Ψ₂Sq : R[X] :=
  C 4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆

lemma C_Ψ₂Sq : C W.Ψ₂Sq = W.ψ₂ ^ 2 - 4 * W.toAffine.polynomial := by
  rw [Ψ₂Sq, ψ₂, b₂, b₄, b₆, Affine.polynomialY, Affine.polynomial]
  C_simp
  ring1

lemma ψ₂_sq : W.ψ₂ ^ 2 = C W.Ψ₂Sq + 4 * W.toAffine.polynomial := by
  simp [C_Ψ₂Sq]

lemma Affine.CoordinateRing.mk_ψ₂_sq : mk W W.ψ₂ ^ 2 = mk W (C W.Ψ₂Sq) := by
  simp [C_Ψ₂Sq]

end Ψ₂Sq

section preΨ'

/-! ### The univariate polynomials `preΨₙ` for `n ∈ ℕ` -/

noncomputable def Ψ₃ : R[X] :=
  3 * X ^ 4 + C W.b₂ * X ^ 3 + 3 * C W.b₄ * X ^ 2 + 3 * C W.b₆ * X + C W.b₈

noncomputable def preΨ₄ : R[X] :=
  2 * X ^ 6 + C W.b₂ * X ^ 5 + 5 * C W.b₄ * X ^ 4 + 10 * C W.b₆ * X ^ 3 + 10 * C W.b₈ * X ^ 2 +
    C (W.b₂ * W.b₈ - W.b₄ * W.b₆) * X + C (W.b₄ * W.b₈ - W.b₆ ^ 2)

noncomputable def preΨ' (n : ℕ) : R[X] :=
  preNormEDS' (W.Ψ₂Sq ^ 2) W.Ψ₃ W.preΨ₄ n
