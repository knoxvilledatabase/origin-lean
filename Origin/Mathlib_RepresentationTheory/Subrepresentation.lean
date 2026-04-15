/-
Extracted from RepresentationTheory/Subrepresentation.lean
Genuine: 3 of 7 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Subrepresentations

This file defines subrepresentations of a monoid representation.

-/

open Pointwise

open scoped MonoidAlgebra

variable {A G W M : Type*}

variable [Semiring A] [Monoid G] [AddCommMonoid W] [Module A W]
  (ρ : Representation A G W) [AddCommMonoid M] [Module A[G] M] in

structure Subrepresentation where
  /-- A subrepresentation is a submodule. -/
  toSubmodule : Submodule A W
  apply_mem_toSubmodule (g : G) ⦃v : W⦄ : v ∈ toSubmodule → ρ g v ∈ toSubmodule

namespace Subrepresentation

section non_comm

variable [Semiring A] [Monoid G] [AddCommMonoid W] [Module A W] {ρ : Representation A G W}
  [AddCommMonoid M] [Module A[G] M]

lemma toSubmodule_injective :
    Function.Injective (toSubmodule : Subrepresentation ρ → Submodule A W) := by
  rintro ⟨_, _⟩
  congr!

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

def toRepresentation (ρ' : Subrepresentation ρ) : Representation A G ρ'.toSubmodule where
  toFun g := (ρ g).restrict (ρ'.apply_mem_toSubmodule g)
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :
