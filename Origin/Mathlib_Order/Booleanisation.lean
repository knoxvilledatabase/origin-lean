/-
Extracted from Order/Booleanisation.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Adding complements to a generalized Boolean algebra

This file embeds any generalized Boolean algebra into a Boolean algebra.

This concretely proves that any equation holding true in the theory of Boolean algebras that does
not reference `ᶜ` also holds true in the theory of generalized Boolean algebras. Put another way,
one does not need the existence of complements to prove something which does not talk about
complements.

## Main declarations

* `Booleanisation`: Boolean algebra containing a given generalised Boolean algebra as a sublattice.
* `Booleanisation.liftLatticeHom`: Boolean algebra containing a given generalised Boolean algebra as
  a sublattice.

## Future work

If mathlib ever acquires `GenBoolAlg`, the category of generalised Boolean algebras, then one could
show that `Booleanisation` is the free functor from `GenBoolAlg` to `BoolAlg`.
-/

open Function

variable {α : Type*}

def Booleanisation (α : Type*) := α ⊕ α

namespace Booleanisation

-- INSTANCE (free from Core): instDecidableEq
