/-
Extracted from Algebra/TrivSqZeroExt/Ideal.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The square zero ideal of the trivial square-zero extension

- `TrivSqZeroExt.kerIdeal`: the ideal in the trivial square-zero extension

- `TrivSqZeroExt.kerIdeal_sq `: this ideal has square zero.

-/

namespace TrivSqZeroExt

open Ideal

variable (R M : Type*)
  [CommSemiring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]

def kerIdeal : Ideal (TrivSqZeroExt R M) := RingHom.ker (fstHom R R M)

theorem mem_kerIdeal_iff_inr (x : TrivSqZeroExt R M) : x ∈ kerIdeal R M ↔ x = inr x.snd := by
  obtain ⟨r, m⟩ := x
  simp only [kerIdeal, RingHom.mem_ker, fstHom_apply, fst_mk]
  exact ⟨fun hr => by rw [hr]; rfl, fun hrm => by rw [← fst_mk r m, hrm, fst_inr]⟩
