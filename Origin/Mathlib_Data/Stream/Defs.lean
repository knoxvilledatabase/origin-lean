/-
Extracted from Data/Stream/Defs.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Definition of `Stream'` and functions on streams

A stream `Stream' α` is an infinite sequence of elements of `α`. One can also think about it as an
infinite list. In this file we define `Stream'` and some functions that take and/or return streams.
Note that we already have `Stream` to represent a similar object, hence the awkward naming.
-/

universe u v w

variable {α : Type u} {β : Type v} {δ : Type w}

def Stream' (α : Type u) := ℕ → α

namespace Stream'

def cons (a : α) (s : Stream' α) : Stream' α
  | 0 => a
  | n + 1 => s n
