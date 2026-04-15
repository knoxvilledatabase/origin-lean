/-
Extracted from Algebra/Module/Submodule/Defs.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!

# Submodules of a module

In this file we define

* `Submodule R M` : a subset of a `Module` `M` that contains zero and is closed with respect to
  addition and scalar multiplication.

* `Subspace k M` : an abbreviation for `Submodule` assuming that `k` is a `Field`.

## Tags

submodule, subspace, linear map
-/

assert_not_exists DivisionRing

open Function

universe u'' u' u v w

variable {G : Type u''} {S : Type u'} {R : Type u} {M : Type v} {ι : Type w}

structure Submodule (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M] : Type v
    extends AddSubmonoid M, SubMulAction R M

add_decl_doc Submodule.toAddSubmonoid

add_decl_doc Submodule.toSubMulAction

namespace Submodule

variable [Semiring R] [AddCommMonoid M] [Module R M]

-- INSTANCE (free from Core): setLike

-- INSTANCE (free from Core): :

initialize_simps_projections Submodule (carrier → coe, as_prefix coe)
