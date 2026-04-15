/-
Extracted from Data/Finset/PImage.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Image of a `Finset α` under a partially defined function

In this file we define `Part.toFinset` and `Finset.pimage`. We also prove some trivial lemmas about
these definitions.

## Tags

finite set, image, partial function
-/

variable {α β : Type*}

namespace Part

def toFinset (o : Part α) [Decidable o.Dom] : Finset α :=
  o.toOption.toFinset
