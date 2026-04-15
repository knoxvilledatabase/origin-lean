/-
Extracted from Order/Fin/Clamp.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Lemmas about `Fin.clamp`

-/

namespace Fin

public lemma clamp_monotone {m : ℕ} : Monotone (fun n ↦ clamp n m) := by
  intro a b h
  rw [le_iff_val_le_val]
  exact min_le_min_right m h

public lemma clamp_eq_last (n m : ℕ) (hmn : m ≤ n) :
    clamp n m = last _ := by
  ext
  simpa

end Fin
