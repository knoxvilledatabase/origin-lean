/-
Extracted from Data/ULift.lean
Genuine: 6 of 11 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-!
# Extra lemmas about `ULift` and `PLift`

In this file we provide `Subsingleton`, `Unique`, `DecidableEq`, and `isEmpty` instances for
`ULift α` and `PLift α`. We also prove `ULift.forall`, `ULift.exists`, `PLift.forall`, and
`PLift.exists`.
-/

universe u v u' v'

open Function

namespace PLift

variable {α : Sort u} {β : Sort v} {f : α → β}

-- INSTANCE (free from Core): [Nonempty

-- INSTANCE (free from Core): [Unique

-- INSTANCE (free from Core): [DecidableEq

-- INSTANCE (free from Core): [IsEmpty

theorem up_injective : Injective (@up α) :=
  Equiv.plift.symm.injective

theorem up_surjective : Surjective (@up α) :=
  Equiv.plift.symm.surjective

theorem up_bijective : Bijective (@up α) :=
  Equiv.plift.symm.bijective

theorem down_surjective : Surjective (@down α) :=
  Equiv.plift.surjective

theorem down_bijective : Bijective (@down α) :=
  Equiv.plift.bijective

theorem «forall» {p : PLift α → Prop} : (∀ x, p x) ↔ ∀ x : α, p (PLift.up x) :=
  up_surjective.forall
