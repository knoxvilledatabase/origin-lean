/-
Extracted from RingTheory/PrincipalIdealDomain.lean
Genuine: 1 of 5 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Principal ideal rings, principal ideal domains, and Bézout rings

A principal ideal ring (PIR) is a ring in which all left ideals are principal. A
principal ideal domain (PID) is an integral domain which is a principal ideal ring.

The definition of `IsPrincipalIdealRing` can be found in `Mathlib/RingTheory/Ideal/Span.lean`.

## Main definitions

Note that for principal ideal domains, one should use
`[IsDomain R] [IsPrincipalIdealRing R]`. There is no explicit definition of a PID.
Theorems about PID's are in the `PrincipalIdealRing` namespace.

- `IsBezout`: the predicate saying that every finitely generated left ideal is principal.
- `generator`: a generator of a principal ideal (or more generally submodule)
- `to_uniqueFactorizationMonoid`: a PID is a unique factorization domain

## Main results

- `Ideal.IsPrime.to_maximal_ideal`: a non-zero prime ideal in a PID is maximal.
- `EuclideanDomain.to_principal_ideal_domain` : a Euclidean domain is a PID.
- `IsBezout.nonemptyGCDMonoid`: Every Bézout domain is a GCD domain.

-/

universe u v

variable {R : Type u} {M : Type v}

open Set Function

open Submodule

variable [Semiring R] [AddCommMonoid M] [Module R M]

-- INSTANCE (free from Core): bot_isPrincipal

-- INSTANCE (free from Core): top_isPrincipal

variable (R)

class IsBezout : Prop where
  /-- Any finitely generated ideal is principal. -/
  isPrincipal_of_FG : ∀ I : Ideal R, I.FG → I.IsPrincipal

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

end

namespace Submodule.IsPrincipal

variable [AddCommMonoid M]

section Semiring

variable [Semiring R] [Module R M]
