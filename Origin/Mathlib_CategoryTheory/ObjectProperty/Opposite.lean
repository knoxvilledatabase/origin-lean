/-
Extracted from CategoryTheory/ObjectProperty/Opposite.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The opposite of a property of objects

-/

universe v u

namespace CategoryTheory.ObjectProperty

open Opposite

variable {C : Type u}

variable [CategoryStruct.{v} C]

protected def op (P : ObjectProperty C) : ObjectProperty Cᵒᵖ :=
  fun X ↦ P X.unop

protected def unop (P : ObjectProperty Cᵒᵖ) : ObjectProperty C :=
  fun X ↦ P (op X)
