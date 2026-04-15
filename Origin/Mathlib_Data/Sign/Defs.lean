/-
Extracted from Data/Sign/Defs.lean
Genuine: 1 of 4 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Sign type

This file defines the type of signs $\{-1, 0, 1\}$ and its basic arithmetic instances.
-/

set_option genSizeOfSpec false in

inductive SignType
  | zero
  | neg
  | pos
  deriving DecidableEq, Inhabited, Fintype

namespace SignType

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :
