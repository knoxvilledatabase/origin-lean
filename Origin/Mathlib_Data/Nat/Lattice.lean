/-
Extracted from Data/Nat/Lattice.lean
Genuine: 4 of 7 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Conditionally complete linear order structure on `ℕ`

In this file we

* define a `ConditionallyCompleteLinearOrderBot` structure on `ℕ`;
* prove a few lemmas about `iSup`/`iInf`/`Set.iUnion`/`Set.iInter` and natural numbers.
-/

assert_not_exists MonoidWithZero

open Set

namespace Nat

open scoped Classical in

-- INSTANCE (free from Core): :

open scoped Classical in

-- INSTANCE (free from Core): :

open scoped Classical in

theorem sInf_def {s : Set ℕ} (h : s.Nonempty) : sInf s = @Nat.find (fun n ↦ n ∈ s) _ h :=
  dif_pos _

open scoped Classical in

theorem sSup_def {s : Set ℕ} (h : ∃ n, ∀ a ∈ s, a ≤ n) :
    sSup s = @Nat.find (fun n ↦ ∀ a ∈ s, a ≤ n) _ h :=
  dif_pos _

theorem sSup_of_not_bddAbove {s : Set ℕ} (h : ¬BddAbove s) : sSup s = 0 :=
  Set.Infinite.Nat.sSup_eq_zero <| Set.infinite_of_not_bddAbove h

lemma iSup_of_not_bddAbove {ι : Sort*} {f : ι → ℕ} (h : ¬ BddAbove (Set.range f)) :
    (⨆ i, f i : ℕ) = 0 := Nat.sSup_of_not_bddAbove h
