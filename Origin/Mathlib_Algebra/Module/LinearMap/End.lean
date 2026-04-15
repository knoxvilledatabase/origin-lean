/-
Extracted from Algebra/Module/LinearMap/End.lean
Genuine: 1 of 5 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Endomorphisms of a module

In this file we define the type of linear endomorphisms of a module over a ring (`Module.End`).
We set up the basic theory,
including the action of `Module.End` on the module we are considering endomorphisms of.

## Main results

* `Module.End.instSemiring` and `Module.End.instRing`: the (semi)ring of endomorphisms formed by
  taking the additive structure above with composition as multiplication.
-/

universe u v

abbrev Module.End (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M] :=
  M →ₗ[R] M

variable {R R₂ S M M₁ M₂ M₃ N₁ : Type*}

open Function LinearMap

/-!
## Monoid structure of endomorphisms
-/

namespace Module.End

variable [Semiring R] [AddCommMonoid M] [AddCommGroup N₁] [Module R M] [Module R N₁]

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :
