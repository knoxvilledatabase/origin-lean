/-
Extracted from GroupTheory/Commensurable.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Commensurability for subgroups

Two subgroups `H` and `K` of a group `G` are commensurable if `H ∩ K` has finite index in both `H`
and `K`.

This file defines commensurability for subgroups of a group `G`. It goes on to prove that
commensurability defines an equivalence relation on subgroups of `G` and finally defines the
commensurator of a subgroup `H` of `G`, which is the elements `g` of `G` such that `gHg⁻¹` is
commensurable with `H`.

## Main definitions

* `Commensurable H K`: the statement that the subgroups `H` and `K` of `G` are commensurable.
* `commensurator H`: the commensurator of a subgroup `H` of `G`.

## Implementation details

We define the commensurator of a subgroup `H` of `G` by first defining it as a subgroup of
`(conjAct G)`, which we call `commensurator'` and then taking the pre-image under
the map `G → (conjAct G)` to obtain our commensurator as a subgroup of `G`.

We define `Commensurable` both for additive and multiplicative groups (in the `AddSubgroup` and
`Subgroup` namespaces respectively); but `Commensurator` is not additivized, since it is not an
interesting concept for abelian groups, and it would be unusual to write a non-abelian group
additively.
-/

open Pointwise

variable {G : Type*} [Group G]

def Subgroup.quotConjEquiv (H K : Subgroup G) (g : ConjAct G) :
    K ⧸ H.subgroupOf K ≃ (g • K : Subgroup G) ⧸ (g • H).subgroupOf (g • K) :=
  Quotient.congr (K.equivSMul g).toEquiv fun a b ↦ by
    dsimp
    rw [← Quotient.eq'', ← Quotient.eq'', QuotientGroup.eq, QuotientGroup.eq,
      mem_subgroupOf, mem_subgroupOf, ← map_inv, ← map_mul, equivSMul_apply_coe]
    exact smul_mem_pointwise_smul_iff.symm
