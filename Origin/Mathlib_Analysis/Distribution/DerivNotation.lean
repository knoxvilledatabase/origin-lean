/-
Extracted from Analysis/Distribution/DerivNotation.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Type classes for derivatives and the Laplacian

In this file we define notation type classes for line derivatives, also known as partial
derivatives, and for the Laplacian.

Moreover, we provide type-classes that encode the linear structure.
We also define the iterated line derivative and prove elementary properties.
We define a Laplacian based on the sum of second derivatives formula and prove that the Laplacian
thus defined is independent of the choice of basis.

Currently, this type class is only used by Schwartz functions. Future uses include derivatives on
test functions, distributions, tempered distributions, and Sobolev spaces (and other generalized
function spaces).
-/

universe u' u v w

variable {ι ι' 𝕜 R V E F V₁ V₂ V₃ : Type*}

/-! ## Line derivative -/

open Fin

class LineDeriv (V : Type u) (E : Type v) (F : outParam (Type w)) where
  /-- `∂_{v} f` is the line derivative of `f` in direction `v`. The meaning of this notation is
  type-dependent. -/
  lineDerivOp : V → E → F

namespace LineDeriv
