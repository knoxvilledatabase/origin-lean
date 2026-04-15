/-
Extracted from RingTheory/Spectrum/Prime/ChevalleyComplexity.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Chevalley's theorem with complexity bound

⚠ For general usage, see `Mathlib/RingTheory/Spectrum/Prime/Chevalley.lean`.

Chevalley's theorem states that if `f : R → S` is a finitely presented ring hom between commutative
rings, then the image of a constructible set in `Spec S` is a constructible set in `Spec R`.

Constructible sets in the prime spectrum of `R[X]` are made of closed sets in the prime spectrum
(using unions, intersections, and complements), which are themselves made from a family of
polynomials.

We say a closed set *has complexity at most `M`* if it can be written as the zero locus of a family
of at most `M` polynomials each of degree at most `M`. We say a constructible set *has complexity
at most `M`* if it can be written as `(C₁ ∪ ... ∪ Cₖ) \ D` where `k ≤ M`, `C₁, ..., Cₖ` are closed
sets of complexity at most `M` and `D` is a closed set.

This file proves a complexity-aware version of Chevalley's theorem, namely that a constructible set
of complexity at most `M` in `Spec R[X₁, ..., Xₘ]` gets mapped under
`f : R[Y₁, ..., Yₙ] → R[X₁, ..., Xₘ]` to a constructible set of complexity `O_{M, m, n}(1)` in
`Spec R[Y₁, ..., Yₙ]`.

The bound `O_{M, m, n}(1)` we find is of tower type.

## Sketch proof

We first show the result in the case of `C : R → R[X]`. We prove this by induction on the number of
components of the form `(C₁ ∪ ... ∪ Cₖ) \ D`, then by induction again on the number of polynomials
used to describe `(C₁ ∪ ... ∪ Cₖ)`. See the (private) lemma `chevalley_polynomialC`.

Secondly, we prove the result in the case of `C : R → R[X₁, ..., Xₘ]` by composing the first result
with itself `m` times. See the (private) lemma `chevalley_mvPolynomialC`.

Note that, if composing the first result for `C : R → R[X₁]` and `C : R[X₁] → R[X₁, X₂]` naïvely,
the second map `C : R[X₁] → R[X₁, X₂]` won't *see* the `X₁`-degree of the polynomials used to
describe the constructible set in `Spec R[X₁]`. One therefore needs to track a subgroup of the ring
which all coefficients of all used polynomials lie in.

Finally, we deduce the result for any `f : R[Y₁, ..., Yₙ] → R[X₁, ..., Xₘ]` by decomposing it into
two maps `C : R[Y₁, ..., Yₙ] → R[X₁, ..., Xₘ, Y₁, ..., Yₙ]` and
`σ : R[X₁, ..., Xₘ, Y₁, ..., Yₙ] → R[X₁, ..., Xₘ]`. See `chevalley_mvPolynomial_mvPolynomial`.

## Main reference

The structure of the proof follows https://stacks.math.columbia.edu/tag/00FE, although they do
not give an explicit bound on the complexity.

-/

variable {R₀ R S M A : Type*} [CommRing R₀] [CommRing R] [Algebra R₀ R] [CommRing S] [Algebra R₀ S]

variable [AddCommGroup M] [Module R M] [CommRing A] [Algebra R A] {n : ℕ}

open Function Localization MvPolynomial Polynomial TensorProduct PrimeSpectrum

open scoped Pointwise

namespace ChevalleyThm

/-! ### The `C : R → R[X]` case -/

namespace PolynomialC

local notation3 "coeff("p")" => Set.range (Polynomial.coeff p)

variable (n) in

private abbrev DegreeType := (Fin n → WithBot ℕ) ×ₗ Prop

variable (R n) in
