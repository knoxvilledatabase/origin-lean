/-
Extracted from LinearAlgebra/Orientation.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Orientations of modules

This file defines orientations of modules.

## Main definitions

* `Orientation` is a type synonym for `Module.Ray` for the case where the module is that of
  alternating maps from a module to its underlying ring.  An orientation may be associated with an
  alternating map or with a basis.

* `Module.Oriented` is a type class for a choice of orientation of a module that is considered
  the positive orientation.

## Implementation notes

`Orientation` is defined for an arbitrary index type, but the main intended use case is when
that index type is a `Fintype` and there exists a basis of the same cardinality.

## References

* https://en.wikipedia.org/wiki/Orientation_(vector_space)

-/

noncomputable section

open Module

section OrderedCommSemiring

variable (R : Type*) [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]

variable (M : Type*) [AddCommMonoid M] [Module R M]

variable {N : Type*} [AddCommMonoid N] [Module R N]

variable (ι ι' : Type*)

abbrev Orientation := Module.Ray R (M [⋀^ι]→ₗ[R] R)

class Module.Oriented where
  /-- Fix a positive orientation. -/
  positiveOrientation : Orientation R M ι

export Module.Oriented (positiveOrientation)

variable {R M}

def Orientation.map (e : M ≃ₗ[R] N) : Orientation R M ι ≃ Orientation R N ι :=
  Module.Ray.map <| AlternatingMap.domLCongr R R ι R e
