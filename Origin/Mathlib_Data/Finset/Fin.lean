/-
Extracted from Data/Finset/Fin.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Finsets in `Fin n`

A few constructions for Finsets in `Fin n`.

## Main declarations

* `Finset.attachFin`: Turns a Finset of naturals strictly less than `n` into a `Finset (Fin n)`.
-/

variable {n : ℕ}

namespace Finset

def attachFin (s : Finset ℕ) {n : ℕ} (h : ∀ m ∈ s, m < n) : Finset (Fin n) :=
  ⟨s.1.pmap (fun a ha ↦ ⟨a, ha⟩) h, s.nodup.pmap fun _ _ _ _ ↦ Fin.val_eq_of_eq⟩
