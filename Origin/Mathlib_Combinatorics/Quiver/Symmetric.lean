/-
Extracted from Combinatorics/Quiver/Symmetric.lean
Genuine: 4 of 5 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
## Symmetric quivers and arrow reversal

This file contains constructions related to symmetric quivers:

* `Symmetrify V` adds formal inverses to each arrow of `V`.
* `HasReverse` is the class of quivers where each arrow has an assigned formal inverse.
* `HasInvolutiveReverse` extends `HasReverse` by requiring that the reverse of the reverse
  is equal to the original arrow.
* `Prefunctor.PreserveReverse` is the class of prefunctors mapping reverses to reverses.
* `Symmetrify.of`, `Symmetrify.lift`, and the associated lemmas witness the universal property
  of `Symmetrify`.
-/

universe v u w v'

namespace Quiver

def Symmetrify (V : Type*) := V

-- INSTANCE (free from Core): symmetrifyQuiver

variable (U V W : Type*) [Quiver.{u} U] [Quiver.{v} V] [Quiver.{w} W]

class HasReverse where
  /-- the map which sends an arrow to its reverse -/
  reverse' : ∀ {a b : V}, (a ⟶ b) → (b ⟶ a)

def reverse {V} [Quiver.{v} V] [HasReverse V] {a b : V} : (a ⟶ b) → (b ⟶ a) :=
  HasReverse.reverse'

class HasInvolutiveReverse extends HasReverse V where
  /-- `reverse` is involutive -/
  inv' : ∀ {a b : V} (f : a ⟶ b), reverse (reverse f) = f

variable {U V W}
