/-
Extracted from GroupTheory/EckmannHilton.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Eckmann-Hilton argument

The Eckmann-Hilton argument says that if a type carries two monoid structures that distribute
over one another, then they are equal, and in addition commutative.
The main application lies in proving that higher homotopy groups (`πₙ` for `n ≥ 2`) are commutative.

## Main declarations

* `EckmannHilton.commMonoid`: If a type carries a unital magma structure that distributes
  over a unital binary operation, then the magma is a commutative monoid.
* `EckmannHilton.commGroup`: If a type carries a group structure that distributes
  over a unital binary operation, then the group is commutative.

-/

universe u

namespace EckmannHilton

variable {X : Type u}

local notation a " <" m:51 "> " b => m a b

structure IsUnital (m : X → X → X) (e : X) : Prop extends Std.LawfulIdentity m e
