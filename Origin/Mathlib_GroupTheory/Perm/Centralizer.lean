/-
Extracted from GroupTheory/Perm/Centralizer.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Centralizer of a permutation and cardinality of conjugacy classes in the symmetric groups

Let `α : Type` with `Fintype α` (and `DecidableEq α`).
The main goal of this file is to compute the cardinality of
conjugacy classes in `Equiv.Perm α`.
Every `g : Equiv.Perm α` has a `g.cycleType : Multiset ℕ`.
By `Equiv.Perm.isConj_iff_cycleType_eq`,
two permutations are conjugate in `Equiv.Perm α` iff
their cycle types are equal.
To compute the cardinality of the conjugacy classes, we could use
a purely combinatorial approach and compute the number of permutations
with given cycle type but we resorted to a more algebraic approach
based on the study of the centralizer of a permutation `g`.

Given `g : Equiv.Perm α`, the conjugacy class of `g` is the orbit
of `g` under the action `ConjAct (Equiv.Perm α)`, and we use the
orbit-stabilizer theorem
(`MulAction.card_orbit_mul_card_stabilizer_eq_card_group`) to reduce
the computation to the computation of the centralizer of `g`, the
subgroup of `Equiv.Perm α` consisting of all permutations which
commute with `g`. It is accessed here as `MulAction.stabilizer
(ConjAct (Equiv.Perm α)) g` and `Subgroup.centralizer_eq_comap_stabilizer`.

We compute this subgroup as follows.

* If `h : Subgroup.centralizer {g}`, then the action of `ConjAct.toConjAct h`
  by conjugation on `Equiv.Perm α` stabilizes `g.cycleFactorsFinset`.
  That induces an action of `Subgroup.centralizer {g}` on
  `g.cycleFactorsFinset` which is defined as an instance.

* This action defines a group morphism `Equiv.Perm.OnCycleFactors.toPermHom g`
  from `Subgroup.centralizer {g}` to `Equiv.Perm g.cycleFactorsFinset`.

* `Equiv.Perm.OnCycleFactors.range_toPermHom'` is the subgroup of
  `Equiv.Perm g.cycleFactorsFinset` consisting of permutations that
  preserve the cardinality of the support.

* `Equiv.Perm.OnCycleFactors.range_toPermHom_eq_range_toPermHom'` shows that
  the range of `Equiv.Perm.OnCycleFactors.toPermHom g`
  is the subgroup `Equiv.Perm.OnCycleFactors.toPermHom_range' g`
  of `Equiv.Perm g.cycleFactorsFinset`.

This is shown by constructing a right inverse
`Equiv.Perm.Basis.toCentralizer`, as established by
`Equiv.Perm.Basis.toPermHom_apply_toCentralizer`.

* `Equiv.Perm.OnCycleFactors.nat_card_range_toPermHom` computes the
  cardinality of `(Equiv.Perm.OnCycleFactors.toPermHom g).range`
  as a product of factorials.

* `Equiv.Perm.OnCycleFactors.mem_ker_toPermHom_iff` proves that
  `k : Subgroup.centralizer {g}` belongs to the kernel of
  `Equiv.Perm.OnCycleFactors.toPermHom g` if and only if it commutes with
  each cycle of `g`.  This is equivalent to the conjunction of two properties:
  * `k` preserves the set of fixed points of `g`;
  * on each cycle `c`, `k` acts as a power of that cycle.

This allows to give a description of the kernel of
`Equiv.Perm.OnCycleFactors.toPermHom g` as the product of a
symmetric group and of a product of cyclic groups.  This analysis
starts with the morphism `Equiv.Perm.OnCycleFactors.kerParam`, its
injectivity `Equiv.Perm.OnCycleFactors.kerParam_injective`, its range
`Equiv.Perm.OnCycleFactors.kerParam_range_eq`, and its cardinality
`Equiv.Perm.OnCycleFactors.kerParam_range_card`.

* `Equiv.Perm.OnCycleFactors.sign_kerParam_apply_apply` computes the signature
  of the permutation induced given by `Equiv.Perm.OnCycleFactors.kerParam`.

* `Equiv.Perm.nat_card_centralizer g` computes the cardinality
  of the centralizer of `g`.

* `Equiv.Perm.card_isConj_mul_eq g` computes the cardinality
  of the conjugacy class of `g`.

* We now can compute the cardinality of the set of permutations with given cycle type.
  The condition for this cardinality to be zero is given by
  `Equiv.Perm.card_of_cycleType_eq_zero_iff`
  which is itself derived from `Equiv.Perm.exists_with_cycleType_iff`.

* `Equiv.Perm.card_of_cycleType_mul_eq m` and `Equiv.Perm.card_of_cycleType m`
  compute this cardinality.

-/

open scoped Finset Pointwise

namespace Equiv.Perm

open MulAction Equiv Subgroup

variable {α : Type*} [DecidableEq α] [Fintype α] {g : Equiv.Perm α}

namespace OnCycleFactors

variable (g)

variable {g} in

lemma Subgroup.Centralizer.toConjAct_smul_mem_cycleFactorsFinset {k c : Perm α}
    (k_mem : k ∈ centralizer {g}) (c_mem : c ∈ g.cycleFactorsFinset) :
    ConjAct.toConjAct k • c ∈ g.cycleFactorsFinset := by
  suffices (g.cycleFactorsFinset : Set (Perm α)) =
    (ConjAct.toConjAct k) • g.cycleFactorsFinset by
    rw [← Finset.mem_coe, this]
    simp only [Set.smul_mem_smul_set_iff, Finset.mem_coe, c_mem]
  have this := cycleFactorsFinset_conj_eq (ConjAct.toConjAct (k : Perm α)) g
  rw [ConjAct.toConjAct_smul, mem_centralizer_singleton_iff.mp k_mem, mul_assoc] at this
  simp only [mul_inv_cancel, mul_one] at this
  conv_lhs => rw [this]
  simp only [Finset.coe_smul_finset]
