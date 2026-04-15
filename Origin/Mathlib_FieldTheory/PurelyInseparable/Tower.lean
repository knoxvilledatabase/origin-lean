/-
Extracted from FieldTheory/PurelyInseparable/Tower.lean
Genuine: 10 of 10 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Tower law for purely inseparable extensions

This file contains results related to `Field.sepDegree`, `Field.insepDegree` and the tower law.

## Main results

- `Field.lift_sepDegree_mul_lift_sepDegree_of_isAlgebraic`: the separable degrees satisfy the
  tower law: $[E:F]_s [K:E]_s = [K:F]_s$.

- `Field.lift_insepDegree_mul_lift_insepDegree_of_isAlgebraic`:
  `Field.finInsepDegree_mul_finInsepDegree_of_isAlgebraic`: the inseparable degrees satisfy the
  tower law: $[E:F]_i [K:E]_i = [K:F]_i$.

- `IntermediateField.sepDegree_adjoin_eq_of_isAlgebraic_of_isPurelyInseparable`,
  `IntermediateField.sepDegree_adjoin_eq_of_isAlgebraic_of_isPurelyInseparable'`:
  if `K / E / F` is a field extension tower, such that `E / F` is purely inseparable, then
  for any subset `S` of `K` such that `F(S) / F` is algebraic, the `E(S) / E` and `F(S) / F` have
  the same separable degree. In particular, if `S` is an intermediate field of `K / F` such that
  `S / F` is algebraic, the `E(S) / E` and `S / F` have the same separable degree.

- `minpoly.map_eq_of_isSeparable_of_isPurelyInseparable`: if `K / E / F` is a field extension tower,
  such that `E / F` is purely inseparable, then for any element `x` of `K` separable over `F`,
  it has the same minimal polynomials over `F` and over `E`.

- `Polynomial.Separable.map_irreducible_of_isPurelyInseparable`: if `E / F` is purely inseparable,
  `f` is a separable irreducible polynomial over `F`, then it is also irreducible over `E`.

## Tags

separable degree, degree, separable closure, purely inseparable

-/

open Polynomial IntermediateField Field

noncomputable section

universe u v w

section TowerLaw

variable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]

variable (K : Type w) [Field K] [Algebra F K]

variable [Algebra E K] [IsScalarTower F E K]

variable {F K} in

theorem LinearIndependent.map_of_isPurelyInseparable_of_isSeparable [IsPurelyInseparable F E]
    {ι : Type*} {v : ι → K} (hsep : ∀ i : ι, IsSeparable F (v i))
    (h : LinearIndependent F v) : LinearIndependent E v := by
  obtain ⟨q, _⟩ := ExpChar.exists F
  haveI := expChar_of_injective_algebraMap (algebraMap F K).injective q
  refine linearIndependent_iff.mpr fun l hl ↦ Finsupp.ext fun i ↦ ?_
  choose f hf using fun i ↦ (isPurelyInseparable_iff_pow_mem F q).1 ‹_› (l i)
  let n := l.support.sup f
  have := (expChar_pow_pos F q n).ne'
  replace hf (i : ι) : l i ^ q ^ n ∈ (algebraMap F E).range := by
    by_cases hs : i ∈ l.support
    · convert pow_mem (hf i) (q ^ (n - f i)) using 1
      rw [← pow_mul, ← pow_add, Nat.add_sub_of_le (Finset.le_sup hs)]
    exact ⟨0, by rw [map_zero, Finsupp.notMem_support_iff.1 hs, zero_pow this]⟩
  choose lF hlF using hf
  let lF₀ := Finsupp.onFinset l.support lF fun i ↦ by
    contrapose
    refine fun hs ↦ (injective_iff_map_eq_zero _).mp (algebraMap F E).injective _ ?_
    rw [hlF, Finsupp.notMem_support_iff.1 hs, zero_pow this]
  replace h := linearIndependent_iff.1 (h.map_pow_expChar_pow_of_isSeparable' q n hsep) lF₀ <| by
    replace hl := congr($hl ^ q ^ n)
    rw [Finsupp.linearCombination_apply, Finsupp.sum, sum_pow_char_pow, zero_pow this] at hl
    rw [← hl, Finsupp.linearCombination_apply,
      Finsupp.onFinset_sum _ (fun _ ↦ by exact zero_smul _ _)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp_rw [Algebra.smul_def, mul_pow, IsScalarTower.algebraMap_apply F E K, hlF, map_pow]
  refine eq_zero_of_pow_eq_zero ((hlF _).symm.trans ?_)
  convert map_zero (algebraMap F E)
  exact congr($h i)

variable {F K} in

theorem IntermediateField.linearDisjoint_of_isPurelyInseparable_of_isSeparable
    [IsPurelyInseparable F E] (S : IntermediateField F K) [Algebra.IsSeparable F S] :
    S.LinearDisjoint E :=
  have ⟨ι, ⟨b⟩⟩ := Module.Basis.exists_basis F S
  .of_basis_left b <| b.linearIndependent.map' S.val.toLinearMap
    (LinearMap.ker_eq_bot_of_injective S.val.injective)
    |>.map_of_isPurelyInseparable_of_isSeparable E fun i ↦ by
      simpa only [IsSeparable, minpoly_eq] using Algebra.IsSeparable.isSeparable F (b i)

namespace Field

lemma sepDegree_eq_of_isPurelyInseparable_of_isSeparable
    [IsPurelyInseparable F E] [Algebra.IsSeparable E K] : sepDegree F K = Module.rank E K := by
  have h := (separableClosure F K).linearDisjoint_of_isPurelyInseparable_of_isSeparable E
    |>.adjoin_rank_eq_rank_left_of_isAlgebraic_left |>.symm
  rwa [separableClosure.adjoin_eq_of_isAlgebraic_of_isSeparable K, rank_top'] at h

lemma lift_rank_mul_lift_sepDegree_of_isSeparable [Algebra.IsSeparable F E] :
    Cardinal.lift.{w} (Module.rank F E) * Cardinal.lift.{v} (sepDegree E K) =
    Cardinal.lift.{v} (sepDegree F K) := by
  rw [sepDegree, sepDegree, separableClosure.eq_restrictScalars_of_isSeparable F E K]
  exact lift_rank_mul_lift_rank F E (separableClosure E K)

lemma rank_mul_sepDegree_of_isSeparable (K : Type v) [Field K] [Algebra F K]
    [Algebra E K] [IsScalarTower F E K] [Algebra.IsSeparable F E] :
    Module.rank F E * sepDegree E K = sepDegree F K := by
  simpa only [Cardinal.lift_id] using lift_rank_mul_lift_sepDegree_of_isSeparable F E K

lemma insepDegree_eq_of_isSeparable [Algebra.IsSeparable F E] :
    insepDegree F K = insepDegree E K := by
  rw [insepDegree, insepDegree, separableClosure.eq_restrictScalars_of_isSeparable F E K]
  rfl

lemma sepDegree_eq_of_isPurelyInseparable [IsPurelyInseparable F E] :
    sepDegree F K = sepDegree E K := by
  convert sepDegree_eq_of_isPurelyInseparable_of_isSeparable F E (separableClosure E K)
  haveI : IsScalarTower F (separableClosure E K) K := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  rw [sepDegree, ← separableClosure.map_eq_of_separableClosure_eq_bot F
    (separableClosure.separableClosure_eq_bot E K)]
  exact (separableClosure F (separableClosure E K)).equivMap
    (IsScalarTower.toAlgHom F (separableClosure E K) K) |>.symm.toLinearEquiv.rank_eq

lemma lift_rank_mul_lift_insepDegree_of_isPurelyInseparable [IsPurelyInseparable F E] :
    Cardinal.lift.{w} (Module.rank F E) * Cardinal.lift.{v} (insepDegree E K) =
    Cardinal.lift.{v} (insepDegree F K) := by
  have h := (separableClosure F K).linearDisjoint_of_isPurelyInseparable_of_isSeparable E
    |>.lift_rank_right_mul_lift_adjoin_rank_eq_of_isAlgebraic_left
  rwa [separableClosure.adjoin_eq_of_isAlgebraic] at h

lemma rank_mul_insepDegree_of_isPurelyInseparable (K : Type v) [Field K] [Algebra F K]
    [Algebra E K] [IsScalarTower F E K] [IsPurelyInseparable F E] :
    Module.rank F E * insepDegree E K = insepDegree F K := by
  simpa only [Cardinal.lift_id] using lift_rank_mul_lift_insepDegree_of_isPurelyInseparable F E K

theorem lift_sepDegree_mul_lift_sepDegree_of_isAlgebraic [Algebra.IsAlgebraic F E] :
    Cardinal.lift.{w} (sepDegree F E) * Cardinal.lift.{v} (sepDegree E K) =
    Cardinal.lift.{v} (sepDegree F K) := by
  have h := lift_rank_mul_lift_sepDegree_of_isSeparable F (separableClosure F E) K
  rwa [sepDegree_eq_of_isPurelyInseparable (separableClosure F E) E K] at h
