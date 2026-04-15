/-
Extracted from Analysis/InnerProductSpace/Completion.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Completion of an inner product space

We show that the separation quotient and the completion of an inner product space are inner
product spaces.
-/

noncomputable section

variable {𝕜 E F : Type*} [RCLike 𝕜]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

section SeparationQuotient

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

theorem Inseparable.inner_eq_inner {x₁ x₂ y₁ y₂ : E}
    (hx : Inseparable x₁ x₂) (hy : Inseparable y₁ y₂) :
    ⟪x₁, y₁⟫ = ⟪x₂, y₂⟫ :=
  ((hx.prod hy).map continuous_inner).eq

namespace SeparationQuotient

-- INSTANCE (free from Core): :
