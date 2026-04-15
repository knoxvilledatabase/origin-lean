/-
Extracted from Data/WSeq/Productive.lean
Genuine: 5 of 10 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-!
# Productive weak sequences

This file defines the property of a weak sequence being productive as never stalling – the next
output always comes after a finite time. Given a productive weak sequence, a regular sequence
(`Seq`) can be derived from it using `toSeq`.
-/

universe u

namespace Stream'.WSeq

variable {α : Type u}

open Function

class Productive (s : WSeq α) : Prop where
  get?_terminates : ∀ n, (get? s n).Terminates

theorem productive_iff (s : WSeq α) : Productive s ↔ ∀ n, (get? s n).Terminates :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

-- INSTANCE (free from Core): get?_terminates

-- INSTANCE (free from Core): head_terminates

-- INSTANCE (free from Core): productive_tail

-- INSTANCE (free from Core): productive_dropn

open Computation

-- INSTANCE (free from Core): productive_ofSeq

theorem productive_congr {s t : WSeq α} (h : s ~ʷ t) : Productive s ↔ Productive t := by
  simp only [productive_iff]; exact forall_congr' fun n => terminates_congr <| get?_congr h _

def toSeq (s : WSeq α) [Productive s] : Seq α :=
  ⟨fun n => (get? s n).get,
   fun {n} h => by
    cases e : Computation.get (get? s (n + 1))
    · assumption
    have := Computation.mem_of_get_eq _ e
    simp only [get?] at this h
    obtain ⟨a', h'⟩ := head_some_of_head_tail_some this
    have := mem_unique h' (@Computation.mem_of_get_eq _ _ _ _ h)
    contradiction⟩

theorem toSeq_ofSeq (s : Seq α) : toSeq (ofSeq s) = s := by
  apply Subtype.ext; funext n
  dsimp [toSeq]; apply get_eq_of_mem
  rw [get?_ofSeq]; apply ret_mem

end Stream'.WSeq
