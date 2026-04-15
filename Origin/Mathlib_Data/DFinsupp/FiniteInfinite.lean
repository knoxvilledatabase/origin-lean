/-
Extracted from Data/DFinsupp/FiniteInfinite.lean
Genuine: 1 of 4 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Finiteness and infiniteness of the `DFinsupp` type

## Main results

* `DFinsupp.fintype`: if the domain and codomain are finite, then `DFinsupp` is finite
* `DFinsupp.infinite_of_left`: if the domain is infinite, then `DFinsupp` is infinite
* `DFinsupp.infinite_of_exists_right`: if one fiber of the codomain is infinite,
  then `DFinsupp` is infinite
-/

universe u u₁ u₂ v v₁ v₂ v₃ w x y l

variable {ι : Type u} {γ : Type w} {β : ι → Type v} {β₁ : ι → Type v₁} {β₂ : ι → Type v₂}

section FiniteInfinite

-- INSTANCE (free from Core): DFinsupp.fintype

-- INSTANCE (free from Core): DFinsupp.infinite_of_left

theorem DFinsupp.infinite_of_exists_right {ι : Sort _} {π : ι → Sort _} (i : ι) [Infinite (π i)]
    [∀ i, Zero (π i)] : Infinite (Π₀ i, π i) :=
  letI := Classical.decEq ι
  Infinite.of_injective (fun j => DFinsupp.single i j) DFinsupp.single_injective

-- INSTANCE (free from Core): DFinsupp.infinite_of_right

end FiniteInfinite
