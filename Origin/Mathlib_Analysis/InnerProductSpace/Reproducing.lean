/-
Extracted from Analysis/InnerProductSpace/Reproducing.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Reproducing Kernel Hilbert Spaces

This file defines vector-valued reproducing Kernel Hilbert spaces, which are Hilbert spaces of
functions, as well as characterizing these spaces in terms of infinite-dimensional
positive semidefinite matrices.

## Main results

- `RKHS`: the class of reproducing kernel Hilbert spaces
- `RKHS.kernel`: the kernel of a RKHS as a matrix.
- `RKHS.kerFun`: the kernel functions of a RKHS.
- `RKHS.kerFun_dense`: the kernel functions are dense in the Hilbert space.
- `RKHS.posSemidef_kernel`: The kernel is positive semidefinite.
- `RKHS.OfKernel`: RKHS constructed from a positive semidefinite matrix.
- `RKHS.kernel_ofKernel`: The kernel of the constructed RKHS is equal to the matrix, this is
    essentially Moore's theorem.

## TODO

- Privatize `RKHS.H₀`

## References
* [Paulsen, Vern I. and Raghupathi, Mrinal,
  *An introduction to the theory of reproducing kernel {H}ilbert spaces*][MR3526117]
-/

public noncomputable section

open ContinuousLinearMap InnerProductSpace Submodule ComplexConjugate

class RKHS (𝕜 : outParam Type*) (H : Type*) (X V : outParam Type*) [RCLike 𝕜]
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] where
  /-- Continuous injection to functions from the reproducing kernel Hilbert space `H` to functions
  from the domain `X` to the Hilbert space `V` -/
  coeCLM (𝕜) : H →L[𝕜] X → V
  coeCLM_injective : Function.Injective (coeCLM : H → X → V)

namespace RKHS

variable {𝕜 : Type*} [RCLike 𝕜]

variable {X : Type*}

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

variable [RKHS 𝕜 H X V]

-- INSTANCE (free from Core): instFunLike
