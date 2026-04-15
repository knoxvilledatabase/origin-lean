/-
Extracted from Data/Vector/Zip.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The `zipWith` operation on vectors.
-/

namespace List

namespace Vector

section ZipWith

variable {α β γ : Type*} {n : ℕ} (f : α → β → γ)

def zipWith : Vector α n → Vector β n → Vector γ n := fun x y => ⟨List.zipWith f x.1 y.1, by simp⟩
