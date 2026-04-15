/-
Extracted from Order/Completion.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Dedekind-MacNeille completion

The Dedekind-MacNeille completion of a partial order is the smallest complete lattice into which it
embeds.

The theory of concept lattices allows for a simple construction. In fact, `DedekindCut α` is simply
an abbreviation for `Concept α α (· ≤ ·)`. This means we don't need to reprove that this is a
complete lattice; instead, the file simply proves that any order embedding into another complete
lattice factors through it.

## Todo

- Build the order isomorphism `DedekindCut ℚ ≃o EReal`.

## Tags

Dedekind completion, Dedekind cut
-/

open Concept Set

variable {α β : Type*}

variable (α) in

abbrev DedekindCut [Preorder α] := Concept α α (· ≤ ·)

namespace DedekindCut

section Preorder

variable [Preorder α] [Preorder β]

abbrev left (A : DedekindCut α) : Set α := A.extent

abbrev right (A : DedekindCut α) : Set α := A.intent
