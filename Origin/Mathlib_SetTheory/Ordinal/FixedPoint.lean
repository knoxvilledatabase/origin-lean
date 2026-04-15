/-
Extracted from SetTheory/Ordinal/FixedPoint.lean
Genuine: 16 of 16 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Fixed points of normal functions

We prove various statements about the fixed points of normal ordinal functions. We state them in
two forms: as statements about indexed families of normal functions, and as statements about a
single normal function.

Moreover, we prove some lemmas about the fixed points of specific normal functions.

## Main definitions and results

* `nfpFamily`, `nfp`: the next fixed point of a (family of) normal function(s).
* `not_bddAbove_fp_family`, `not_bddAbove_fp`: the (common) fixed points of a (family of) normal
  function(s) are unbounded in the ordinals.
* `deriv_add_eq_mul_omega0_add`: a characterization of the derivative of addition.
* `deriv_mul_eq_opow_omega0_mul`: a characterization of the derivative of multiplication.
-/

noncomputable section

universe u v

open Function Order

namespace Ordinal

/-! ### Fixed points of type-indexed families of ordinals -/

variable {ι : Type*} {f : ι → Ordinal.{u} → Ordinal.{u}}

def nfpFamily (f : ι → Ordinal.{u} → Ordinal.{u}) (a : Ordinal.{u}) : Ordinal :=
  ⨆ i, List.foldr f a i

theorem foldr_le_nfpFamily [Small.{u} ι] (f : ι → Ordinal.{u} → Ordinal.{u}) (a l) :
    List.foldr f a l ≤ nfpFamily f a :=
  Ordinal.le_iSup _ _

theorem le_nfpFamily [Small.{u} ι] (f : ι → Ordinal.{u} → Ordinal.{u}) (a) : a ≤ nfpFamily f a :=
  foldr_le_nfpFamily f a []

theorem lt_nfpFamily_iff [Small.{u} ι] {a b} : a < nfpFamily f b ↔ ∃ l, a < List.foldr f b l :=
  Ordinal.lt_iSup_iff

theorem nfpFamily_le_iff [Small.{u} ι] {a b} : nfpFamily f a ≤ b ↔ ∀ l, List.foldr f a l ≤ b :=
  Ordinal.iSup_le_iff

theorem nfpFamily_le {a b} : (∀ l, List.foldr f a l ≤ b) → nfpFamily f a ≤ b :=
  Ordinal.iSup_le

theorem nfpFamily_monotone [Small.{u} ι] (hf : ∀ i, Monotone (f i)) : Monotone (nfpFamily f) :=
  fun _ _ h ↦ nfpFamily_le <| fun l ↦ (List.foldr_monotone hf l h).trans (foldr_le_nfpFamily _ _ l)

theorem apply_lt_nfpFamily [Small.{u} ι] (H : ∀ i, IsNormal (f i)) {a b}
    (hb : b < nfpFamily f a) (i) : f i b < nfpFamily f a :=
  let ⟨l, hl⟩ := lt_nfpFamily_iff.1 hb
  lt_nfpFamily_iff.2 ⟨i::l, (H i).strictMono hl⟩

theorem apply_lt_nfpFamily_iff [Nonempty ι] [Small.{u} ι] (H : ∀ i, IsNormal (f i)) {a b} :
    (∀ i, f i b < nfpFamily f a) ↔ b < nfpFamily f a := by
  refine ⟨fun h ↦ ?_, apply_lt_nfpFamily H⟩
  let ⟨l, hl⟩ := lt_nfpFamily_iff.1 (h (Classical.arbitrary ι))
  exact lt_nfpFamily_iff.2 <| ⟨l, (H _).strictMono.le_apply.trans_lt hl⟩

theorem nfpFamily_le_apply [Nonempty ι] [Small.{u} ι] (H : ∀ i, IsNormal (f i)) {a b} :
    (∃ i, nfpFamily f a ≤ f i b) ↔ nfpFamily f a ≤ b := by
  contrapose!; exact apply_lt_nfpFamily_iff H

theorem nfpFamily_le_fp (H : ∀ i, Monotone (f i)) {a b} (ab : a ≤ b) (h : ∀ i, f i b ≤ b) :
    nfpFamily f a ≤ b := by
  apply Ordinal.iSup_le fun l ↦ ?_
  induction l generalizing a with
  | nil => exact ab
  | cons i l IH => exact (H i (IH ab)).trans (h i)

theorem nfpFamily_fp [Small.{u} ι] {i} (H : IsNormal (f i)) (a) :
    f i (nfpFamily f a) = nfpFamily f a := by
  rw [nfpFamily, H.map_iSup (bddAbove_of_small _)]
  apply le_antisymm <;> refine Ordinal.iSup_le fun l => ?_
  · exact Ordinal.le_iSup _ (i::l)
  · exact H.strictMono.le_apply.trans (Ordinal.le_iSup _ _)

theorem apply_le_nfpFamily [Small.{u} ι] [hι : Nonempty ι] (H : ∀ i, IsNormal (f i)) {a b} :
    (∀ i, f i b ≤ nfpFamily f a) ↔ b ≤ nfpFamily f a := by
  refine ⟨fun h => ?_, fun h i => ?_⟩
  · obtain ⟨i⟩ := hι
    exact (H i).strictMono.le_apply.trans (h i)
  · rw [← nfpFamily_fp (H i)]
    exact (H i).monotone h

theorem nfpFamily_eq_self [Small.{u} ι] {a} (h : ∀ i, f i a = a) : nfpFamily f a = a := by
  apply (Ordinal.iSup_le ?_).antisymm (le_nfpFamily f a)
  intro l
  rw [List.foldr_fixed' h l]

theorem not_bddAbove_fp_family [Small.{u} ι] (H : ∀ i, IsNormal (f i)) :
    ¬ BddAbove (⋂ i, Function.fixedPoints (f i)) := by
  rw [not_bddAbove_iff]
  refine fun a ↦ ⟨nfpFamily f (succ a), ?_, (lt_succ a).trans_le (le_nfpFamily f _)⟩
  rintro _ ⟨i, rfl⟩
  exact nfpFamily_fp (H i) _

def derivFamily (f : ι → Ordinal.{u} → Ordinal.{u}) (o : Ordinal.{u}) : Ordinal.{u} :=
  limitRecOn o (nfpFamily f 0) (fun _ IH => nfpFamily f (succ IH))
    fun a _ g => ⨆ b : Set.Iio a, g _ b.2
