/-
Extracted from CategoryTheory/ObjectProperty/Retract.lean
Genuine: 2 of 6 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-! # Properties of objects which are stable under retracts

Given a category `C` and `P : ObjectProperty C` (i.e. `P : C → Prop`),
this file introduces the type class `P.IsStableUnderRetracts`.
-/

universe w v u

namespace CategoryTheory.ObjectProperty

open Limits

variable {C : Type u} [Category.{v} C] (P : ObjectProperty C)

class IsStableUnderRetracts where
  of_retract {X Y : C} (_ : Retract X Y) (_ : P Y) : P X

lemma prop_of_retract [IsStableUnderRetracts P] {X Y : C} (h : Retract X Y) (hY : P Y) : P X :=
  IsStableUnderRetracts.of_retract h hY

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

namespace IsStableUnderRetracts

open scoped ZeroObject

variable [P.IsStableUnderRetracts]

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): (priority
