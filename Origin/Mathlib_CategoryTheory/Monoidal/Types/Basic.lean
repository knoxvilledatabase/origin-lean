/-
Extracted from CategoryTheory/Monoidal/Types/Basic.lean
Genuine: 1 of 5 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# The category of types is a (symmetric) monoidal category
-/

open CategoryTheory Limits MonoidalCategory

universe v u

namespace CategoryTheory

-- INSTANCE (free from Core): typesCartesianMonoidalCategory

-- INSTANCE (free from Core): :

attribute [local simp] types_tensorObj_def types_tensorUnit_def
