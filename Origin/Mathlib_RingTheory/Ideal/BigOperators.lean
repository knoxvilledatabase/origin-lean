/-
Extracted from RingTheory/Ideal/BigOperators.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Big operators for ideals

This contains some results on the big operators `∑` and `∏` interacting with the `Ideal` type.
-/

universe u v w

variable {α : Type u} {β : Type v} {F : Type w}

namespace Ideal

variable [Semiring α] (I : Ideal α) {a b : α}

theorem sum_mem (I : Ideal α) {ι : Type*} {t : Finset ι} {f : ι → α} :
    (∀ c ∈ t, f c ∈ I) → (∑ i ∈ t, f i) ∈ I :=
  Submodule.sum_mem I

end Ideal
