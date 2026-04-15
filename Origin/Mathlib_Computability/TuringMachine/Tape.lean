/-
Extracted from Computability/TuringMachine/Tape.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Turing machine tapes

This file defines the notion of a Turing machine tape, and the operations on it. A tape is a
bidirectional infinite sequence of cells, each of which stores an element of a given alphabet `Γ`.
All but finitely many of the cells are required to hold the blank symbol `default : Γ`.

## Main definitions

* `ListBlank Γ` is the type of one-directional tapes with alphabet `Γ`. Implemented as a quotient
  of `List Γ` by extension by blanks at the end.
* `Tape Γ` is the type of Turing machine tapes with alphabet `Γ`. Implemented as two
  `ListBlank Γ` instances, one for each direction, as well as a head symbol.

-/

assert_not_exists MonoidWithZero

open Function (iterate_succ iterate_succ_apply iterate_zero_apply)

namespace Turing

section ListBlank

def BlankExtends {Γ} [Inhabited Γ] (l₁ l₂ : List Γ) : Prop :=
  ∃ n, l₂ = l₁ ++ List.replicate n default
