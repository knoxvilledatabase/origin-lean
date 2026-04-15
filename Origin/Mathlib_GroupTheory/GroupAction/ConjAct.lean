/-
Extracted from GroupTheory/GroupAction/ConjAct.lean
Genuine: 1 of 4 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Conjugation action of a group on itself

This file defines the conjugation action of a group on itself. See also `MulAut.conj` for
the definition of conjugation as a homomorphism into the automorphism group.

## Main definitions

A type alias `ConjAct G` is introduced for a group `G`. The group `ConjAct G` acts on `G`
by conjugation. The group `ConjAct G` also acts on any normal subgroup of `G` by conjugation.

As a generalization, this also allows:
* `ConjAct Mˣ` to act on `M`, when `M` is a `Monoid`
* `ConjAct G₀` to act on `G₀`, when `G₀` is a `GroupWithZero`

## Implementation Notes

The scalar action in defined in this file can also be written using `MulAut.conj g • h`. This
has the advantage of not using the type alias `ConjAct`, but the downside of this approach
is that some theorems about the group actions will not apply when since this
`MulAut.conj g • h` describes an action of `MulAut G` on `G`, and not an action of `G`.

-/

assert_not_exists MonoidWithZero

variable (α M G : Type*)

def ConjAct : Type _ :=
  G

namespace ConjAct

open MulAction Subgroup

variable {M G}

-- INSTANCE (free from Core): [Group

-- INSTANCE (free from Core): [DivInvMonoid

-- INSTANCE (free from Core): [Fintype
