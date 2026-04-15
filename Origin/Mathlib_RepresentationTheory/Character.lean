/-
Extracted from RepresentationTheory/Character.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Characters of representations

This file introduces characters of representation and proves basic lemmas about how characters
behave under various operations on representations.

A key result is the orthogonality of characters for irreducible representations of finite group
over an algebraically closed field whose characteristic doesn't divide the order of the group. It
is the theorem `char_orthonormal`

## Implementation notes

Irreducible representations are implemented categorically, using the `CategoryTheory.Simple` class
defined in `Mathlib/CategoryTheory/Simple.lean`

## TODO
* Once we have the monoidal closed structure on `FdRep k G` and a better API for the rigid
  structure, `char_dual` and `char_linHom` should probably be stated
  in terms of `Vᘁ` and `ihom V W`.
-/

noncomputable section

universe u

open CategoryTheory LinearMap CategoryTheory.MonoidalCategory Representation Module

variable {k : Type u} [Field k]

namespace FDRep

section Monoid

variable {G : Type u} [Monoid G]

def character (V : FDRep k G) (g : G) :=
  LinearMap.trace k V (V.ρ g)

theorem char_mul_comm (V : FDRep k G) (g : G) (h : G) :
    V.character (h * g) = V.character (g * h) := by simp only [trace_mul_comm, character, map_mul]
