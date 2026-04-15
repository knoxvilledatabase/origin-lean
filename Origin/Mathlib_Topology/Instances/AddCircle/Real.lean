/-
Extracted from Topology/Instances/AddCircle/Real.lean
Genuine: 6 of 9 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# The additive circle over `ℝ`

Results specific to the additive circle over `ℝ`.
-/

noncomputable section

open AddCommGroup Set Function AddSubgroup TopologicalSpace Topology

namespace AddCircle

variable (p : ℝ)

-- INSTANCE (free from Core): pathConnectedSpace

-- INSTANCE (free from Core): compactSpace

-- INSTANCE (free from Core): :

end AddCircle

section UnitAddCircle

abbrev UnitAddCircle :=
  AddCircle (1 : ℝ)

end UnitAddCircle

namespace ZMod

variable {N : ℕ} [NeZero N]

noncomputable def toAddCircle : ZMod N →+ UnitAddCircle :=
  lift N ⟨AddMonoidHom.mk' (fun j ↦ ↑(j / N : ℝ)) (by simp [add_div]),
    by simp [div_self (NeZero.ne _)]⟩

lemma toAddCircle_intCast (j : ℤ) :
    toAddCircle (j : ZMod N) = ↑(j / N : ℝ) := by
  simp [toAddCircle]

lemma toAddCircle_natCast (j : ℕ) :
    toAddCircle (j : ZMod N) = ↑(j / N : ℝ) := by
  simpa using toAddCircle_intCast (N := N) j

lemma toAddCircle_apply (j : ZMod N) :
    toAddCircle j = ↑(j.val / N : ℝ) := by
  rw [← toAddCircle_natCast, natCast_zmod_val]

variable (N) in

lemma toAddCircle_injective : Function.Injective (toAddCircle : ZMod N → _) := by
  intro x y hxy
  have : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos _)
  rwa [toAddCircle_apply, toAddCircle_apply, AddCircle.coe_eq_coe_iff_of_mem_Ico,
    div_left_inj' this.ne', Nat.cast_inj, (val_injective N).eq_iff] at hxy <;>
  exact ⟨by positivity, by simpa only [zero_add, div_lt_one this, Nat.cast_lt] using val_lt _⟩
