/-
Extracted from CategoryTheory/Bicategory/End.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Endomorphisms of an object in a bicategory, as a monoidal category.
-/

universe w v u

namespace CategoryTheory

variable {C : Type u} [Bicategory.{w, v} C]

abbrev EndMonoidal (X : C) :=
  X ⟶ X

-- INSTANCE (free from Core): (X

-- INSTANCE (free from Core): (X

open Bicategory

open MonoidalCategory
