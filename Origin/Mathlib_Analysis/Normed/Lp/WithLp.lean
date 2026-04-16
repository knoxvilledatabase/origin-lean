/-
Extracted from Analysis/Normed/Lp/WithLp.lean
Genuine: 3 | Conflates: 0 | Dissolved: 0 | Infrastructure: 17
-/
import Origin.Core
import Mathlib.Data.ENNReal.Basic
import Mathlib.RingTheory.Finiteness.Defs

noncomputable section

/-! # The `WithLp` type synonym

`WithLp p V` is a copy of `V` with exactly the same vector space structure, but with the Lp norm
instead of any existing norm on `V`; recall that by default `ι → R` and `R × R` are equipped with
a norm defined as the supremum of the norms of their components.

This file defines the vector space structure for all types `V`; the norm structure is built for
different specializations of `V` in downstream files.

Note that this should not be used for infinite products, as in these cases the "right" Lp spaces is
not the same as the direct product of the spaces. See the docstring in `Mathlib/Analysis/PiLp` for
more details.

## Main definitions

* `WithLp p V`: a copy of `V` to be equipped with an L`p` norm.
* `WithLp.equiv p V`: the canonical equivalence between `WithLp p V` and `V`.
* `WithLp.linearEquiv p K V`: the canonical `K`-module isomorphism between `WithLp p V` and `V`.

## Implementation notes

The pattern here is the same one as is used by `Lex` for order structures; it avoids having a
separate synonym for each type (`ProdLp`, `PiLp`, etc), and allows all the structure-copying code
to be shared.

TODO: is it safe to copy across the topology and uniform space structure too for all reasonable
choices of `V`?
-/

open scoped ENNReal

universe uK uK' uV

@[nolint unusedArguments]
def WithLp (_p : ℝ≥0∞) (V : Type uV) : Type uV := V

variable (p : ℝ≥0∞) (K : Type uK) (K' : Type uK') (V : Type uV)

namespace WithLp

protected def equiv : WithLp p V ≃ V := Equiv.refl _

instance instNontrivial [Nontrivial V] : Nontrivial (WithLp p V) := ‹Nontrivial V›

instance instUnique [Unique V] : Unique (WithLp p V) := ‹Unique V›

variable [Semiring K] [Semiring K'] [AddCommGroup V]

/-! `WithLp p V` inherits various module-adjacent structures from `V`. -/

instance instAddCommGroup : AddCommGroup (WithLp p V) := ‹AddCommGroup V›

instance instModule [Module K V] : Module K (WithLp p V) := ‹Module K V›

instance instIsScalarTower [SMul K K'] [Module K V] [Module K' V] [IsScalarTower K K' V] :
    IsScalarTower K K' (WithLp p V) :=
  ‹IsScalarTower K K' V›

instance instSMulCommClass [Module K V] [Module K' V] [SMulCommClass K K' V] :
    SMulCommClass K K' (WithLp p V) :=
  ‹SMulCommClass K K' V›

instance instModuleFinite [Module K V] [Module.Finite K V] : Module.Finite K (WithLp p V) :=
  ‹Module.Finite K V›

variable {K V}

variable [Module K V]

variable (c : K) (x y : WithLp p V) (x' y' : V)

/-! `WithLp.equiv` preserves the module structure. -/

variable (K V)

@[simps (config := .asFn)]
protected def linearEquiv : WithLp p V ≃ₗ[K] V :=
  { LinearEquiv.refl _ _ with
    toFun := WithLp.equiv _ _
    invFun := (WithLp.equiv _ _).symm }

end WithLp
