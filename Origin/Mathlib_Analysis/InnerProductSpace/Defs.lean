/-
Extracted from Analysis/InnerProductSpace/Defs.lean
Genuine: 4 of 5 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Inner product spaces

This file defines inner product spaces.
Hilbert spaces can be obtained using the set of assumptions
`[RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]`.
For convenience, a variable alias `HilbertSpace` is provided so that one can write
`variable? [HilbertSpace 𝕜 E]` and get this as a suggestion.

An inner product space is a vector space endowed with an inner product. It generalizes the notion of
dot product in `ℝ^n` and provides the means of defining the length of a vector and the angle between
two vectors. In particular vectors `x` and `y` are orthogonal if their inner product equals zero.
We define both the real and complex cases at the same time using the `RCLike` typeclass.

Rather than defining the norm on an inner product space to be `√(re ⟪x, x⟫)`, we assume that a norm
is given, and add a hypothesis stating that `‖x‖ ^ 2 = re ⟪x, x⟫`. This makes it possible to
handle spaces where the norm is equal, but not defeq, to the square root of the
inner product. Defining a norm starting from an inner product is handled via the
`InnerProductSpace.Core` structure.

This file is intended to contain the minimal amount of machinery needed to define inner product
spaces, and to construct a normed space from an inner product space. Many more general lemmas can
be found in `Analysis.InnerProductSpace.Basic`. For the specific construction of an inner product
structure on `n → 𝕜` for `𝕜 = ℝ` or `ℂ`, see `EuclideanSpace` in
`Analysis.InnerProductSpace.PiL2`.

## Main results

- We define the class `InnerProductSpace 𝕜 E` extending `NormedSpace 𝕜 E` with a number of basic
  properties, most notably the Cauchy-Schwarz inequality. Here `𝕜` is understood to be either `ℝ`
  or `ℂ`, through the `RCLike` typeclass.

## Notation

We globally denote the real and complex inner products by `⟪·, ·⟫_ℝ` and `⟪·, ·⟫_ℂ` respectively.
We also provide two notation namespaces: `RealInnerProductSpace`, `ComplexInnerProductSpace`,
which respectively introduce the plain notation `⟪·, ·⟫` for the real and complex inner product.

## Implementation notes

We choose the convention that inner products are conjugate linear in the first argument and linear
in the second.

## Tags

inner product space, Hilbert space, norm

## References
* [Clément & Martin, *The Lax-Milgram Theorem. A detailed proof to be formalized in Coq*]
* [Clément & Martin, *A Coq formal proof of the Lax–Milgram theorem*]

The Coq code is available at the following address: <http://www.lri.fr/~sboldo/elfic/index.html>
-/

noncomputable section

open RCLike Real Filter Topology ComplexConjugate Finsupp Bornology

open LinearMap (BilinForm)

variable {𝕜 E F : Type*} [RCLike 𝕜]

class Inner (𝕜 E : Type*) where
  /-- The inner product function. -/
  inner (𝕜) : E → E → 𝕜

export Inner (inner)

scoped[InnerProductSpace] notation:max "⟪" x ", " y "⟫_" 𝕜:max => inner 𝕜 x y

section Notations

scoped[RealInnerProductSpace] notation "⟪" x ", " y "⟫" => inner ℝ x y

scoped[ComplexInnerProductSpace] notation "⟪" x ", " y "⟫" => inner ℂ x y

end Notations

class InnerProductSpace (𝕜 : Type*) (E : Type*) [RCLike 𝕜] [SeminormedAddCommGroup E] extends
    NormedSpace 𝕜 E, Inner 𝕜 E where
  /-- The inner product induces the norm. -/
  norm_sq_eq_re_inner : ∀ x : E, ‖x‖ ^ 2 = re (inner x x)
  /-- The inner product is *Hermitian*, taking the `conj` swaps the arguments. -/
  conj_inner_symm : ∀ x y, conj (inner y x) = inner x y
  /-- The inner product is additive in the first coordinate. -/
  add_left : ∀ x y z, inner (x + y) z = inner x z + inner y z
  /-- The inner product is conjugate linear in the first coordinate. -/
  smul_left : ∀ x y r, inner (r • x) y = conj r * inner x y

/-!
### Constructing a normed space structure from an inner product

In the definition of an inner product space, we require the existence of a norm, which is equal
(but maybe not defeq) to the square root of the scalar product. This makes it possible to put
an inner product space structure on spaces with a preexisting norm (for instance `ℝ`), with good
properties. However, sometimes, one would like to define the norm starting only from a well-behaved
scalar product. This is what we implement in this paragraph, starting from a structure
`InnerProductSpace.Core` stating that we have a nice scalar product.

Our goal here is not to develop a whole theory with all the supporting API, as this will be done
below for `InnerProductSpace`. Instead, we implement the bare minimum to go as directly as
possible to the construction of the norm and the proof of the triangular inequality.

Warning: Do not use this `Core` structure if the space you are interested in already has a norm
instance defined on it, otherwise this will create a second non-defeq norm instance!
-/

structure PreInnerProductSpace.Core (𝕜 : Type*) (F : Type*) [RCLike 𝕜] [AddCommGroup F]
    [Module 𝕜 F] extends Inner 𝕜 F where
  /-- The inner product is *Hermitian*, taking the `conj` swaps the arguments. -/
  conj_inner_symm x y : conj (inner y x) = inner x y
  /-- The inner product is positive (semi)definite. -/
  re_inner_nonneg x : 0 ≤ re (inner x x)
  /-- The inner product is additive in the first coordinate. -/
  add_left x y z : inner (x + y) z = inner x z + inner y z
  /-- The inner product is conjugate linear in the first coordinate. -/
  smul_left x y r : inner (r • x) y = conj r * inner x y

attribute [class] PreInnerProductSpace.Core

structure InnerProductSpace.Core (𝕜 : Type*) (F : Type*) [RCLike 𝕜] [AddCommGroup F]
  [Module 𝕜 F] extends PreInnerProductSpace.Core 𝕜 F where
  /-- The inner product is positive definite. -/
  definite : ∀ x, inner x x = 0 → x = 0

attribute [class] InnerProductSpace.Core

-- INSTANCE (free from Core): (𝕜
