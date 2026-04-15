/-
Extracted from Data/NNReal/Basic.lean
Genuine: 26 | Conflates: 0 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Canonical.Basic
import Mathlib.Algebra.Order.Nonneg.Floor
import Mathlib.Data.Real.Pointwise
import Mathlib.Data.NNReal.Defs
import Mathlib.Order.ConditionallyCompleteLattice.Group

/-!
# Basic results on nonnegative real numbers

This file contains all results on `NNReal` that do not directly follow from its basic structure.
As a consequence, it is a bit of a random collection of results, and is a good target for cleanup.

## Notations

This file uses `ℝ≥0` as a localized notation for `NNReal`.
-/

open Function

open scoped BigOperators

namespace NNReal

noncomputable instance : FloorSemiring ℝ≥0 := Nonneg.floorSemiring

@[simp, norm_cast]
theorem coe_indicator {α} (s : Set α) (f : α → ℝ≥0) (a : α) :
    ((s.indicator f a : ℝ≥0) : ℝ) = s.indicator (fun x => ↑(f x)) a :=
  (toRealHom : ℝ≥0 →+ ℝ).map_indicator _ _ _

@[norm_cast]
theorem coe_list_sum (l : List ℝ≥0) : ((l.sum : ℝ≥0) : ℝ) = (l.map (↑)).sum :=
  map_list_sum toRealHom l

@[norm_cast]
theorem coe_list_prod (l : List ℝ≥0) : ((l.prod : ℝ≥0) : ℝ) = (l.map (↑)).prod :=
  map_list_prod toRealHom l

@[norm_cast]
theorem coe_multiset_sum (s : Multiset ℝ≥0) : ((s.sum : ℝ≥0) : ℝ) = (s.map (↑)).sum :=
  map_multiset_sum toRealHom s

@[norm_cast]
theorem coe_multiset_prod (s : Multiset ℝ≥0) : ((s.prod : ℝ≥0) : ℝ) = (s.map (↑)).prod :=
  map_multiset_prod toRealHom s

variable {ι : Type*} {s : Finset ι} {f : ι → ℝ}

@[simp, norm_cast]
theorem coe_sum (s : Finset ι) (f : ι → ℝ≥0) : ∑ i ∈ s, f i = ∑ i ∈ s, (f i : ℝ) :=
  map_sum toRealHom _ _

@[simp, norm_cast]
lemma coe_expect (s : Finset ι) (f : ι → ℝ≥0) : 𝔼 i ∈ s, f i = 𝔼 i ∈ s, (f i : ℝ) :=
  map_expect toRealHom ..

theorem _root_.Real.toNNReal_sum_of_nonneg (hf : ∀ i ∈ s, 0 ≤ f i) :
    Real.toNNReal (∑ a ∈ s, f a) = ∑ a ∈ s, Real.toNNReal (f a) := by
  rw [← coe_inj, NNReal.coe_sum, Real.coe_toNNReal _ (Finset.sum_nonneg hf)]
  exact Finset.sum_congr rfl fun x hxs => by rw [Real.coe_toNNReal _ (hf x hxs)]

@[simp, norm_cast]
theorem coe_prod (s : Finset ι) (f : ι → ℝ≥0) : ↑(∏ a ∈ s, f a) = ∏ a ∈ s, (f a : ℝ) :=
  map_prod toRealHom _ _

theorem _root_.Real.toNNReal_prod_of_nonneg (hf : ∀ a, a ∈ s → 0 ≤ f a) :
    Real.toNNReal (∏ a ∈ s, f a) = ∏ a ∈ s, Real.toNNReal (f a) := by
  rw [← coe_inj, NNReal.coe_prod, Real.coe_toNNReal _ (Finset.prod_nonneg hf)]
  exact Finset.prod_congr rfl fun x hxs => by rw [Real.coe_toNNReal _ (hf x hxs)]

theorem le_iInf_add_iInf {ι ι' : Sort*} [Nonempty ι] [Nonempty ι'] {f : ι → ℝ≥0} {g : ι' → ℝ≥0}
    {a : ℝ≥0} (h : ∀ i j, a ≤ f i + g j) : a ≤ (⨅ i, f i) + ⨅ j, g j := by
  rw [← NNReal.coe_le_coe, NNReal.coe_add, coe_iInf, coe_iInf]
  exact le_ciInf_add_ciInf h

theorem mul_finset_sup {α} (r : ℝ≥0) (s : Finset α) (f : α → ℝ≥0) :
    r * s.sup f = s.sup fun a => r * f a :=
  Finset.comp_sup_eq_sup_comp _ (NNReal.mul_sup r) (mul_zero r)

theorem finset_sup_mul {α} (s : Finset α) (f : α → ℝ≥0) (r : ℝ≥0) :
    s.sup f * r = s.sup fun a => f a * r :=
  Finset.comp_sup_eq_sup_comp (· * r) (fun x y => NNReal.sup_mul x y r) (zero_mul r)

theorem finset_sup_div {α} {f : α → ℝ≥0} {s : Finset α} (r : ℝ≥0) :
    s.sup f / r = s.sup fun a => f a / r := by simp only [div_eq_inv_mul, mul_finset_sup]

open Real

section Sub

/-!
### Lemmas about subtraction

In this section we provide a few lemmas about subtraction that do not fit well into any other
typeclass. For lemmas about subtraction and addition see lemmas about `OrderedSub` in the file
`Mathlib.Algebra.Order.Sub.Basic`. See also `mul_tsub` and `tsub_mul`.
-/

theorem sub_div (a b c : ℝ≥0) : (a - b) / c = a / c - b / c :=
  tsub_div _ _ _

end Sub

section Csupr

open Set

variable {ι : Sort*} {f : ι → ℝ≥0}

theorem iInf_mul (f : ι → ℝ≥0) (a : ℝ≥0) : iInf f * a = ⨅ i, f i * a := by
  rw [← coe_inj, NNReal.coe_mul, coe_iInf, coe_iInf]
  exact Real.iInf_mul_of_nonneg (NNReal.coe_nonneg _) _

theorem mul_iInf (f : ι → ℝ≥0) (a : ℝ≥0) : a * iInf f = ⨅ i, a * f i := by
  simpa only [mul_comm] using iInf_mul f a

theorem mul_iSup (f : ι → ℝ≥0) (a : ℝ≥0) : (a * ⨆ i, f i) = ⨆ i, a * f i := by
  rw [← coe_inj, NNReal.coe_mul, NNReal.coe_iSup, NNReal.coe_iSup]
  exact Real.mul_iSup_of_nonneg (NNReal.coe_nonneg _) _

theorem iSup_mul (f : ι → ℝ≥0) (a : ℝ≥0) : (⨆ i, f i) * a = ⨆ i, f i * a := by
  rw [mul_comm, mul_iSup]
  simp_rw [mul_comm]

theorem iSup_div (f : ι → ℝ≥0) (a : ℝ≥0) : (⨆ i, f i) / a = ⨆ i, f i / a := by
  simp only [div_eq_mul_inv, iSup_mul]

theorem mul_iSup_le {a : ℝ≥0} {g : ℝ≥0} {h : ι → ℝ≥0} (H : ∀ j, g * h j ≤ a) : g * iSup h ≤ a := by
  rw [mul_iSup]
  exact ciSup_le' H

theorem iSup_mul_le {a : ℝ≥0} {g : ι → ℝ≥0} {h : ℝ≥0} (H : ∀ i, g i * h ≤ a) : iSup g * h ≤ a := by
  rw [iSup_mul]
  exact ciSup_le' H

theorem iSup_mul_iSup_le {a : ℝ≥0} {g h : ι → ℝ≥0} (H : ∀ i j, g i * h j ≤ a) :
    iSup g * iSup h ≤ a :=
  iSup_mul_le fun _ => mul_iSup_le <| H _

variable [Nonempty ι]

theorem le_mul_iInf {a : ℝ≥0} {g : ℝ≥0} {h : ι → ℝ≥0} (H : ∀ j, a ≤ g * h j) : a ≤ g * iInf h := by
  rw [mul_iInf]
  exact le_ciInf H

theorem le_iInf_mul {a : ℝ≥0} {g : ι → ℝ≥0} {h : ℝ≥0} (H : ∀ i, a ≤ g i * h) : a ≤ iInf g * h := by
  rw [iInf_mul]
  exact le_ciInf H

theorem le_iInf_mul_iInf {a : ℝ≥0} {g h : ι → ℝ≥0} (H : ∀ i j, a ≤ g i * h j) :
    a ≤ iInf g * iInf h :=
  le_iInf_mul fun i => le_mul_iInf <| H i

end Csupr

end NNReal
