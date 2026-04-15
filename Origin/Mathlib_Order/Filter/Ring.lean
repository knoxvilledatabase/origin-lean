/-
Extracted from Order/Filter/Ring.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Lemmas about filters and ordered rings.
-/

namespace Filter

open Function Filter

universe u v

variable {α : Type u} {β : Type v}

theorem EventuallyLE.mul_le_mul [MulZeroClass β] [Preorder β] [PosMulMono β] [MulPosMono β]
    {l : Filter α} {f₁ f₂ g₁ g₂ : α → β} (hf : f₁ ≤ᶠ[l] f₂) (hg : g₁ ≤ᶠ[l] g₂) (hg₀ : 0 ≤ᶠ[l] g₁)
    (hf₀ : 0 ≤ᶠ[l] f₂) : f₁ * g₁ ≤ᶠ[l] f₂ * g₂ := by
  filter_upwards [hf, hg, hg₀, hf₀] with x using _root_.mul_le_mul
