/-
Extracted from RingTheory/Noetherian/Nilpotent.lean
Genuine: 1 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.RingTheory.Noetherian.Defs

noncomputable section

/-!
# Nilpotent ideals in Noetherian rings


## Main results

* `IsNoetherianRing.isNilpotent_nilradical`
-/

open IsNoetherian

theorem IsNoetherianRing.isNilpotent_nilradical (R : Type*) [CommRing R] [IsNoetherianRing R] :
    IsNilpotent (nilradical R) := by
  obtain ⟨n, hn⟩ := Ideal.exists_radical_pow_le_of_fg (⊥ : Ideal R) (IsNoetherian.noetherian _)
  exact ⟨n, eq_bot_iff.mpr hn⟩
