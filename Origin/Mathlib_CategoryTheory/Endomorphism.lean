/-
Extracted from CategoryTheory/Endomorphism.lean
Genuine: 3 of 6 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Endomorphisms

Definition and basic properties of endomorphisms and automorphisms of an object in a category.

For each `X : C`, we provide `CategoryTheory.End X := X ⟶ X` with a monoid structure,
and `CategoryTheory.Aut X := X ≅ X` with a group structure.
-/

universe v v' u u'

namespace CategoryTheory

def End {C : Type u} [CategoryStruct.{v} C] (X : C) := X ⟶ X

namespace End

section Struct

variable {C : Type u} [CategoryStruct.{v} C] (X : C)

-- INSTANCE (free from Core): one

-- INSTANCE (free from Core): inhabited

-- INSTANCE (free from Core): mul

variable {X}

abbrev of (f : X ⟶ X) : End X := f

abbrev asHom (f : End X) : X ⟶ X := f
