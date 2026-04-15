/-
Extracted from GroupTheory/Perm/ConjAct.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Some lemmas pertaining to the action of `ConjAct (Perm α)` on `Perm α`

We prove some lemmas related to the action of `ConjAct (Perm α)` on `Perm α`:

Let `α` be a decidable fintype.

* `conj_support_eq` relates the support of `k • g` with that of `g`

* `cycleFactorsFinset_conj_eq`, `mem_cycleFactorsFinset_conj'`
  and `cycleFactorsFinset_conj` relate the set of cycles of `g`, `g.cycleFactorsFinset`,
  with that for `k • g`

-/

namespace Equiv.Perm

open scoped Pointwise

variable {α : Type*} [DecidableEq α] [Fintype α]

theorem mem_conj_support (k : ConjAct (Perm α)) (g : Perm α) (a : α) :
    a ∈ (k • g).support ↔ ConjAct.ofConjAct k⁻¹ a ∈ g.support := by
  simp only [mem_support, ConjAct.smul_def, not_iff_not, coe_mul,
    Function.comp_apply, ConjAct.ofConjAct_inv]
  apply Equiv.apply_eq_iff_eq_symm_apply

theorem support_conj_eq_smul_support (k : ConjAct (Perm α)) (g : Equiv.Perm α) :
    (k • g).support = k.ofConjAct • g.support := by
  ext
  rw [mem_conj_support, ← Perm.smul_def, ConjAct.ofConjAct_inv, Finset.inv_smul_mem_iff]

theorem cycleFactorsFinset_conj (g k : Perm α) :
    (ConjAct.toConjAct k • g).cycleFactorsFinset =
      Finset.map (MulAut.conj k).toEquiv.toEmbedding g.cycleFactorsFinset := by
  ext c
  rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct, Finset.mem_map_equiv,
    ← mem_cycleFactorsFinset_conj g k]
  -- We avoid `group` here to minimize imports while low in the hierarchy;
  -- typically it would be better to invoke the tactic.
  simp [mul_assoc]
