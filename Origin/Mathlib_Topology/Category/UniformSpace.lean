/-
Extracted from Topology/Category/UniformSpace.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# The category of uniform spaces

We construct the category of uniform spaces, show that the complete separated uniform spaces
form a reflective subcategory, and hence possess all limits that uniform spaces do.

TODO: show that uniform spaces actually have all limits!
-/

universe u

open CategoryTheory

structure UniformSpaceCat : Type (u + 1) where
  /-- Construct a bundled `UniformSpace` from the underlying type and the typeclass. -/
  of ::
  /-- The underlying uniform space. -/
  carrier : Type u
  [str : UniformSpace carrier]

attribute [instance] UniformSpaceCat.str

namespace UniformSpaceCat

-- INSTANCE (free from Core): :
