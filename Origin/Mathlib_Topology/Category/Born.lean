/-
Extracted from Topology/Category/Born.lean
Genuine: 1 of 5 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# The category of bornologies

This defines `Born`, the category of bornologies.
-/

universe u

open CategoryTheory

structure Born where
  /-- Construct a bundled `Born` from a `Bornology`. -/
  of ::
  /-- The underlying bornology. -/
  carrier : Type*
  [str : Bornology carrier]

attribute [instance] Born.str

namespace Born

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

end Born
