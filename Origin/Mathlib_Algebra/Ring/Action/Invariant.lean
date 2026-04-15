/-
Extracted from Algebra/Ring/Action/Invariant.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-! # Subrings invariant under an action

If a monoid acts on a ring via a `MulSemiringAction`, then `IsInvariantSubring` is
a predicate on subrings asserting that the subring is fixed elementwise by the
action.

-/

assert_not_exists RelIso

section Ring

variable (M R : Type*) [Monoid M] [Ring R] [MulSemiringAction M R]

variable (S : Subring R)

open MulAction

variable {R}

class IsInvariantSubring : Prop where
  smul_mem : ∀ (m : M) {x : R}, x ∈ S → m • x ∈ S

-- INSTANCE (free from Core): IsInvariantSubring.toMulSemiringAction

end Ring

variable (M : Type*) [Monoid M]

variable {R' : Type*} [Ring R'] [MulSemiringAction M R']

variable (U : Subring R') [IsInvariantSubring M U]

def IsInvariantSubring.subtypeHom : U →+*[M] R' :=
  { U.subtype with map_smul' := fun _ _ ↦ rfl }
