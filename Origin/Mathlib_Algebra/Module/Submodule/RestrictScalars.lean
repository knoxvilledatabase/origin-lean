/-
Extracted from Algebra/Module/Submodule/RestrictScalars.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Restriction of scalars for submodules

If semiring `S` acts on a semiring `R` and `M` is a module over both (compatibly with this action)
then we can turn an `R`-submodule into an `S`-submodule by forgetting the action of `R`. We call
this restriction of scalars for submodules.

## Main definitions:
* `Submodule.restrictScalars`: regard an `R`-submodule as an `S`-submodule if `S` acts on `R`

-/

namespace Submodule

variable (S : Type*) {R M : Type*} [Semiring R] [AddCommMonoid M] [Semiring S]
  [Module S M] [Module R M] [SMul S R] [IsScalarTower S R M]

def restrictScalars (V : Submodule R M) : Submodule S M where
  carrier := V
  zero_mem' := V.zero_mem
  smul_mem' c _ h := V.smul_of_tower_mem c h
  add_mem' hx hy := V.add_mem hx hy
