/-
Extracted from Topology/Order/Category/AlexDisc.lean
Genuine: 2 of 9 | Dissolved: 0 | Infrastructure: 7
-/
import Origin.Core

/-!
# Category of Alexandrov-discrete topological spaces

This defines `AlexDisc`, the category of Alexandrov-discrete topological spaces with continuous
maps, and proves it's equivalent to the category of preorders.
-/

open CategoryTheory Topology

structure AlexDisc extends TopCat where
  [is_alexandrovDiscrete : AlexandrovDiscrete carrier]

namespace AlexDisc

attribute [instance] is_alexandrovDiscrete

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): category

-- INSTANCE (free from Core): concreteCategory

-- INSTANCE (free from Core): instHasForgetToTop

-- INSTANCE (free from Core): forgetToTop_full

-- INSTANCE (free from Core): forgetToTop_faithful

abbrev of (X : Type*) [TopologicalSpace X] [AlexandrovDiscrete X] : AlexDisc where
  toTopCat := TopCat.of X
