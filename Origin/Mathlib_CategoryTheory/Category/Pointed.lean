/-
Extracted from CategoryTheory/Category/Pointed.lean
Genuine: 2 of 5 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# The category of pointed types

This defines `Pointed`, the category of pointed types.

## TODO

* Monoidal structure
* Upgrade `typeToPointed` to an equivalence
-/

open CategoryTheory

universe u

structure Pointed : Type (u + 1) where
  /-- the underlying type -/
  protected X : Type u
  /-- the distinguished element -/
  point : X

namespace Pointed

-- INSTANCE (free from Core): :

abbrev of {X : Type*} (point : X) : Pointed :=
  ⟨X, point⟩

alias _root_.Prod.Pointed := of

-- INSTANCE (free from Core): :
