/-
Extracted from Data/ZMod/Units.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Lemmas about units in `ZMod`.
-/

assert_not_exists TwoSidedIdeal

namespace ZMod

variable {n m : ℕ}

def unitsMap (hm : n ∣ m) : (ZMod m)ˣ →* (ZMod n)ˣ := Units.map (castHom hm (ZMod n))

lemma unitsMap_comp {d : ℕ} (hm : n ∣ m) (hd : m ∣ d) :
    (unitsMap hm).comp (unitsMap hd) = unitsMap (dvd_trans hm hd) := by
  simp only [unitsMap_def]
  rw [← Units.map_comp]
  exact congr_arg Units.map <| congr_arg RingHom.toMonoidHom <| castHom_comp hm hd
