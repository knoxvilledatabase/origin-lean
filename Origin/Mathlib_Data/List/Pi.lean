/-
Extracted from Data/List/Pi.lean
Genuine: 4 of 5 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# The Cartesian product of lists

## Main definitions

* `List.pi`: Cartesian product of lists indexed by a list.
-/

namespace List

namespace Pi

variable {ι : Type*} [DecidableEq ι] {α : ι → Sort*}

def nil (α : ι → Sort*) : (∀ i ∈ ([] : List ι), α i) :=
  nofun

variable {i : ι} {l : List ι}

def head (f : ∀ j ∈ i :: l, α j) : α i :=
  f i mem_cons_self

def tail (f : ∀ j ∈ i :: l, α j) : ∀ j ∈ l, α j :=
  fun j hj ↦ f j (mem_cons_of_mem _ hj)

variable (i l)

def cons (a : α i) (f : ∀ j ∈ l, α j) : ∀ j ∈ i :: l, α j :=
  Multiset.Pi.cons (α := ι) l _ a f

variable {i l}
