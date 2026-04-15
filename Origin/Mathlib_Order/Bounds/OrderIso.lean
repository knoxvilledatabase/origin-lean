/-
Extracted from Order/Bounds/OrderIso.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Order isomorphisms and bounds.
-/

open Set

namespace OrderIso

variable {α β : Type*} [Preorder α] [Preorder β] (f : α ≃o β)

theorem upperBounds_image {s : Set α} : upperBounds (f '' s) = f '' upperBounds s :=
  Subset.antisymm
    (fun x hx =>
      ⟨f.symm x, fun _ hy => f.le_symm_apply.2 (hx <| mem_image_of_mem _ hy), f.apply_symm_apply x⟩)
    f.monotone.image_upperBounds_subset_upperBounds_image

theorem lowerBounds_image {s : Set α} : lowerBounds (f '' s) = f '' lowerBounds s :=
  @upperBounds_image αᵒᵈ βᵒᵈ _ _ f.dual _
