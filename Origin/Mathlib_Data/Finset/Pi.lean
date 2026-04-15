/-
Extracted from Data/Finset/Pi.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The Cartesian product of finsets

## Main definitions

* `Finset.pi`: Cartesian product of finsets indexed by a finset.
-/

open Function

namespace Finset

open Multiset

/-! ### pi -/

section Pi

variable {α : Type*}

def Pi.empty (β : α → Sort*) (a : α) (h : a ∈ (∅ : Finset α)) : β a :=
  Multiset.Pi.empty β a h

universe u v

variable {β : α → Type u} {δ : α → Sort v} {s : Finset α} {t : ∀ a, Finset (β a)}

variable [DecidableEq α]

def pi (s : Finset α) (t : ∀ a, Finset (β a)) : Finset (∀ a ∈ s, β a) :=
  ⟨s.1.pi fun a => (t a).1, s.nodup.pi fun a _ => (t a).nodup⟩
