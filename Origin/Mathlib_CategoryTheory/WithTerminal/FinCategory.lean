/-
Extracted from CategoryTheory/WithTerminal/FinCategory.lean
Genuine: 2 of 6 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!

# `WithTerminal C` and `WithInitial C` are finite whenever `C` is

If `C` has finitely many objects, then so do `WithTerminal C` and `WithInitial C`,
and likewise if `C` has finitely many morphisms as well.

-/

universe v u

variable (C : Type u) [CategoryTheory.Category.{v} C]

namespace CategoryTheory.WithTerminal

def optionEquiv : Option C ≃ WithTerminal C where
  toFun
  | some a => of a
  | none => star
  invFun
  | of a => some a
  | star => none
  left_inv a := by cases a <;> simp
  right_inv a := by cases a <;> simp

-- INSTANCE (free from Core): instFintype

-- INSTANCE (free from Core): instFinCategory

end CategoryTheory.WithTerminal

namespace CategoryTheory.WithInitial

def optionEquiv : Option C ≃ WithInitial C where
  toFun
  | some a => of a
  | none => star
  invFun
  | of a => some a
  | star => none
  left_inv a := by cases a <;> simp
  right_inv a := by cases a <;> simp

-- INSTANCE (free from Core): instFintype

-- INSTANCE (free from Core): instFinCategory

end CategoryTheory.WithInitial
