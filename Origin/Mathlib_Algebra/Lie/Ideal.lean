/-
Extracted from Algebra/Lie/Ideal.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Lie Ideals

This file defines Lie ideals, which are Lie submodules of a Lie algebra over itself.
They are defined as a special case of `LieSubmodule`, and inherit much of their structure from it.

We also prove some basic properties of Lie ideals, including how they behave under
Lie algebra homomorphisms (`map`, `comap`) and how they relate to the lattice structure
on Lie submodules.

## Main definitions

* `LieIdeal`
* `LieIdeal.map`
* `LieIdeal.comap`

## Tags

Lie algebra, ideal, submodule, Lie submodule
-/

universe u v w w₁ w₂

section LieSubmodule

variable (R : Type u) (L : Type v) (M : Type w)

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

section LieIdeal

variable [LieAlgebra R L] [LieModule R L M]

abbrev LieIdeal :=
  LieSubmodule R L L

theorem lie_mem_right (I : LieIdeal R L) (x y : L) (h : y ∈ I) : ⁅x, y⁆ ∈ I :=
  I.lie_mem h

theorem lie_mem_left (I : LieIdeal R L) (x y : L) (h : x ∈ I) : ⁅x, y⁆ ∈ I := by
  rw [← lie_skew, ← neg_lie]; apply lie_mem_right; assumption

def LieIdeal.toLieSubalgebra (I : LieIdeal R L) : LieSubalgebra R L :=
  { I.toSubmodule with lie_mem' := by intro x y _ hy; apply lie_mem_right; exact hy }
