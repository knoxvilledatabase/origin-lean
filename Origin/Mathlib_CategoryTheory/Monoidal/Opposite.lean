/-
Extracted from CategoryTheory/Monoidal/Opposite.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Monoidal opposites

We write `Cᵐᵒᵖ` for the monoidal opposite of a monoidal category `C`.
-/

universe v₁ v₂ u₁ u₂

variable {C : Type u₁}

namespace CategoryTheory

open CategoryTheory.MonoidalCategory

structure MonoidalOpposite (C : Type u₁) where
  /-- The object of `MonoidalOpposite C` that represents `x : C`. -/ mop ::
  /-- The object of `C` represented by `x : MonoidalOpposite C`. -/ unmop : C

namespace MonoidalOpposite
