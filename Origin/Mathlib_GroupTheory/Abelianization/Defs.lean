/-
Extracted from GroupTheory/Abelianization/Defs.lean
Genuine: 2 of 4 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# The abelianization of a group

This file defines the commutator and the abelianization of a group. It furthermore prepares for the
result that the abelianization is left adjoint to the forgetful functor from abelian groups to
groups, which can be found in `Mathlib/Algebra/Category/Grp/Adjunctions.lean`.

## Main definitions

* `Abelianization`: defines the abelianization of a group `G` as the quotient of a group by its
  commutator subgroup.
* `Abelianization.map`: lifts a group homomorphism to a homomorphism between the abelianizations
* `MulEquiv.abelianizationCongr`: Equivalent groups have equivalent abelianizations

-/

assert_not_exists Cardinal Field

universe u v w

variable (G : Type u) [Group G]

open Subgroup (centralizer)

def Abelianization : Type u :=
  G ⧸ commutator G

namespace Abelianization

attribute [local instance] QuotientGroup.leftRel

-- INSTANCE (free from Core): commGroup

-- INSTANCE (free from Core): :

variable {G}

def of : G →* Abelianization G where
  toFun := QuotientGroup.mk
  map_one' := rfl
  map_mul' _ _ := rfl
