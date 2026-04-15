/-
Extracted from RingTheory/Length.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Length of modules

## Main results
- `Module.length`: `Module.length R M` is the length of `M` as an `R`-module.
- `Module.length_pos`: The length of a nontrivial module is positive
- `Module.length_ne_top`: The length of an Artinian and Noetherian module is finite.
- `Module.length_eq_add_of_exact`: Length is additive in exact sequences.

-/

variable (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]

noncomputable

def Module.length : ℕ∞ :=
  (Order.krullDim (Submodule R M)).unbot (by simp [Order.krullDim_eq_bot_iff])

lemma Module.coe_length :
    (Module.length R M : WithBot ℕ∞) = Order.krullDim (Submodule R M) :=
  WithBot.coe_unbot _ _

lemma Module.length_eq_height : Module.length R M = Order.height (⊤ : Submodule R M) := by
  apply WithBot.coe_injective
  rw [Module.coe_length, Order.height_top_eq_krullDim]

lemma Module.length_eq_coheight : Module.length R M = Order.coheight (⊥ : Submodule R M) := by
  apply WithBot.coe_injective
  rw [Module.coe_length, Order.coheight_bot_eq_krullDim]

variable {R M}

lemma Module.length_eq_zero_iff : Module.length R M = 0 ↔ Subsingleton M := by
  rw [← WithBot.coe_inj, Module.coe_length, WithBot.coe_zero,
    Order.krullDim_eq_zero_iff_of_orderTop, Submodule.subsingleton_iff]
