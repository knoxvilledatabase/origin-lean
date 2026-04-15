/-
Extracted from Topology/Category/Locale.lean
Genuine: 2 of 4 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# The category of locales

This file defines `Locale`, the category of locales. This is the opposite of the category of frames.
-/

universe u

open CategoryTheory Opposite Order TopologicalSpace

def Locale :=
  Frmᵒᵖ deriving LargeCategory

namespace Locale

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): (X

def of (α : Type*) [Frame α] : Locale :=
  op <| Frm.of α
