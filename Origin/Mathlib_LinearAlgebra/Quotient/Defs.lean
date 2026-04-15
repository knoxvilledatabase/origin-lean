/-
Extracted from LinearAlgebra/Quotient/Defs.lean
Genuine: 5 of 12 | Dissolved: 0 | Infrastructure: 7
-/
import Origin.Core

/-!
# Quotients by submodules

* If `p` is a submodule of `M`, `M ⧸ p` is the quotient of `M` with respect to `p`:
  that is, elements of `M` are identified if their difference is in `p`. This is itself a module.

## Main definitions

* `Submodule.Quotient.mk`: a function sending an element of `M` to `M ⧸ p`
* `Submodule.Quotient.module`: `M ⧸ p` is a module
* `Submodule.Quotient.mkQ`: a linear map sending an element of `M` to `M ⧸ p`
* `Submodule.quotEquivOfEq`: if `p` and `p'` are equal, their quotients are equivalent

-/

section Ring

namespace Submodule

variable {R M : Type*} {r : R} {x y : M} [Ring R] [AddCommGroup M] [Module R M]

variable (p p' : Submodule R M)

open QuotientAddGroup

def quotientRel : Setoid M :=
  QuotientAddGroup.leftRel p.toAddSubgroup

set_option backward.isDefEq.respectTransparency false in

theorem quotientRel_def {x y : M} : p.quotientRel x y ↔ x - y ∈ p :=
  Iff.trans
    (by
      rw [leftRel_apply, sub_eq_add_neg, neg_add, neg_neg]
      rfl)
    neg_mem_iff

-- INSTANCE (free from Core): hasQuotient

namespace Quotient

def mk {p : Submodule R M} : M → M ⧸ p :=
  Quotient.mk''

protected theorem eq' {x y : M} : (mk x : M ⧸ p) = mk y ↔ -x + y ∈ p :=
  QuotientAddGroup.eq

protected theorem eq {x y : M} : (mk x : M ⧸ p) = mk y ↔ x - y ∈ p :=
  (Submodule.Quotient.eq' p).trans (leftRel_apply.symm.trans p.quotientRel_def)

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :
