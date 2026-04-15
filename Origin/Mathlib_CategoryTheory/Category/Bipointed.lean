/-
Extracted from CategoryTheory/Category/Bipointed.lean
Genuine: 2 of 5 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# The category of bipointed types

This defines `Bipointed`, the category of bipointed types.

## TODO

Monoidal structure
-/

open CategoryTheory

universe u

structure Bipointed : Type (u + 1) where
  /-- The underlying type of a bipointed type. -/
  protected X : Type u
  /-- The two points of a bipointed type, bundled together as a pair. -/
  toProd : X × X

namespace Bipointed

-- INSTANCE (free from Core): :

abbrev of {X : Type*} (to_prod : X × X) : Bipointed :=
  ⟨X, to_prod⟩

alias _root_.Prod.Bipointed := of

-- INSTANCE (free from Core): :
