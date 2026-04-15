/-
Extracted from Order/BooleanSubalgebra.lean
Genuine: 2 of 4 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Boolean subalgebras

This file defines Boolean subalgebras.
-/

open Function Set

variable {ι : Sort*} {α β γ : Type*}

variable (α) in

structure BooleanSubalgebra [BooleanAlgebra α] extends Sublattice α where
  compl_mem' {a} : a ∈ carrier → aᶜ ∈ carrier
  bot_mem' : ⊥ ∈ carrier

namespace BooleanSubalgebra

section BooleanAlgebra

variable [BooleanAlgebra α] [BooleanAlgebra β] [BooleanAlgebra γ] {L M : BooleanSubalgebra α}
  {f : BoundedLatticeHom α β} {s t : Set α} {a b : α}

initialize_simps_projections BooleanSubalgebra (carrier → coe, as_prefix coe)

-- INSTANCE (free from Core): instSetLike

-- INSTANCE (free from Core): :

lemma coe_inj : (L : Set α) = M ↔ L = M := SetLike.coe_set_eq
