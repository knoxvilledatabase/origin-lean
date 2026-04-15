/-
Extracted from Analysis/Normed/Operator/LinearIsometry.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# (Semi-)linear isometries

In this file we define `LinearIsometry σ₁₂ E E₂` (notation: `E →ₛₗᵢ[σ₁₂] E₂`) to be a semilinear
isometric embedding of `E` into `E₂` and `LinearIsometryEquiv` (notation: `E ≃ₛₗᵢ[σ₁₂] E₂`) to be
a semilinear isometric equivalence between `E` and `E₂`.  The notation for the associated purely
linear concepts is `E →ₗᵢ[R] E₂`, `E ≃ₗᵢ[R] E₂`, and `E →ₗᵢ⋆[R] E₂`, `E ≃ₗᵢ⋆[R] E₂` for
the star-linear versions.

We also prove some trivial lemmas and provide convenience constructors.

Since a lot of elementary properties don't require `‖x‖ = 0 → x = 0` we start setting up the
theory for `SeminormedAddCommGroup` and we specialize to `NormedAddCommGroup` when needed.
-/

open Function Set Topology

variable {R R₂ R₃ R₄ E E₂ E₃ E₄ F 𝓕 : Type*} [Semiring R] [Semiring R₂] [Semiring R₃] [Semiring R₄]
  {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R} {σ₁₃ : R →+* R₃} {σ₃₁ : R₃ →+* R} {σ₁₄ : R →+* R₄}
  {σ₄₁ : R₄ →+* R} {σ₂₃ : R₂ →+* R₃} {σ₃₂ : R₃ →+* R₂} {σ₂₄ : R₂ →+* R₄} {σ₄₂ : R₄ →+* R₂}
  {σ₃₄ : R₃ →+* R₄} {σ₄₃ : R₄ →+* R₃} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
  [RingHomInvPair σ₁₃ σ₃₁] [RingHomInvPair σ₃₁ σ₁₃] [RingHomInvPair σ₂₃ σ₃₂]
  [RingHomInvPair σ₃₂ σ₂₃] [RingHomInvPair σ₁₄ σ₄₁] [RingHomInvPair σ₄₁ σ₁₄]
  [RingHomInvPair σ₂₄ σ₄₂] [RingHomInvPair σ₄₂ σ₂₄] [RingHomInvPair σ₃₄ σ₄₃]
  [RingHomInvPair σ₄₃ σ₃₄] [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomCompTriple σ₁₂ σ₂₄ σ₁₄]
  [RingHomCompTriple σ₂₃ σ₃₄ σ₂₄] [RingHomCompTriple σ₁₃ σ₃₄ σ₁₄] [RingHomCompTriple σ₃₂ σ₂₁ σ₃₁]
  [RingHomCompTriple σ₄₂ σ₂₁ σ₄₁] [RingHomCompTriple σ₄₃ σ₃₂ σ₄₂] [RingHomCompTriple σ₄₃ σ₃₁ σ₄₁]
  [SeminormedAddCommGroup E] [SeminormedAddCommGroup E₂] [SeminormedAddCommGroup E₃]
  [SeminormedAddCommGroup E₄] [Module R E] [Module R₂ E₂] [Module R₃ E₃] [Module R₄ E₄]
  [NormedAddCommGroup F] [Module R F]

structure LinearIsometry (σ₁₂ : R →+* R₂) (E E₂ : Type*) [SeminormedAddCommGroup E]
  [SeminormedAddCommGroup E₂] [Module R E] [Module R₂ E₂] extends E →ₛₗ[σ₁₂] E₂ where
  norm_map' : ∀ x, ‖toLinearMap x‖ = ‖x‖
