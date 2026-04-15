/-
Extracted from Data/Nat/Nth.lean
Genuine: 11 of 11 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The `n`th Number Satisfying a Predicate

This file defines a function for "what is the `n`th number that satisfies a given predicate `p`",
and provides lemmas that deal with this function and its connection to `Nat.count`.

## Main definitions

* `Nat.nth p n`: The `n`-th natural `k` (zero-indexed) such that `p k`. If there is no
  such natural (that is, `p` is true for at most `n` naturals), then `Nat.nth p n = 0`.

## Main results

* `Nat.nth_eq_orderEmbOfFin`: For a finitely-often true `p`, gives the cardinality of the set of
  numbers satisfying `p` above particular values of `nth p`
* `Nat.gc_count_nth`: Establishes a Galois connection between `Nat.nth p` and `Nat.count p`.
* `Nat.nth_eq_orderIsoOfNat`: For an infinitely-often true predicate, `nth` agrees with the
  order-isomorphism of the subtype to the natural numbers.

## Implementation details

Much of the below was written before `Set.encard` existed and partly for this reason uses the
pattern `∀ hf : Set.Finite (setOf p), n < hf.toFinset.card` rather than `n < {x | p x}.encard`.
We should consider changing this.

There has been some discussion on the subject of whether both of `nth` and
`Nat.Subtype.orderIsoOfNat` should exist. See discussion
[here](https://github.com/leanprover-community/mathlib/pull/9457#pullrequestreview-767221180).
Future work should address how lemmas that use these should be written.

-/

open Finset

namespace Nat

variable (p : ℕ → Prop)

noncomputable def nth (p : ℕ → Prop) (n : ℕ) : ℕ := by
  classical exact
    if h : Set.Finite (setOf p) then h.toFinset.sort.getD n 0
    else @Nat.Subtype.orderIsoOfNat (setOf p) (Set.Infinite.to_subtype h) n

variable {p}

/-!
### Lemmas about `Nat.nth` on a finite set
-/

theorem nth_of_card_le (hf : (setOf p).Finite) {n : ℕ} (hn : #hf.toFinset ≤ n) :
    nth p n = 0 := by rw [nth, dif_pos hf, List.getD_eq_default]; rwa [Finset.length_sort]

theorem nth_eq_getD_sort (h : (setOf p).Finite) (n : ℕ) :
    nth p n = h.toFinset.sort.getD n 0 :=
  dif_pos h

theorem nth_eq_orderEmbOfFin (hf : (setOf p).Finite) {n : ℕ} (hn : n < #hf.toFinset) :
    nth p n = hf.toFinset.orderEmbOfFin rfl ⟨n, hn⟩ := by
  rw [nth_eq_getD_sort hf, Finset.orderEmbOfFin_apply, List.getD_eq_getElem, Fin.getElem_fin]

theorem nth_strictMonoOn (hf : (setOf p).Finite) :
    StrictMonoOn (nth p) (Set.Iio #hf.toFinset) := by
  rintro m (hm : m < _) n (hn : n < _) h
  simp only [nth_eq_orderEmbOfFin, *]
  exact OrderEmbedding.strictMono _ h

theorem nth_lt_nth_of_lt_card (hf : (setOf p).Finite) {m n : ℕ} (h : m < n)
    (hn : n < #hf.toFinset) : nth p m < nth p n :=
  nth_strictMonoOn hf (h.trans hn) hn h

theorem nth_le_nth_of_lt_card (hf : (setOf p).Finite) {m n : ℕ} (h : m ≤ n)
    (hn : n < #hf.toFinset) : nth p m ≤ nth p n :=
  (nth_strictMonoOn hf).monotoneOn (h.trans_lt hn) hn h

theorem lt_of_nth_lt_nth_of_lt_card (hf : (setOf p).Finite) {m n : ℕ} (h : nth p m < nth p n)
    (hm : m < #hf.toFinset) : m < n :=
  not_le.1 fun hle => h.not_ge <| nth_le_nth_of_lt_card hf hle hm

theorem le_of_nth_le_nth_of_lt_card (hf : (setOf p).Finite) {m n : ℕ} (h : nth p m ≤ nth p n)
    (hm : m < #hf.toFinset) : m ≤ n :=
  not_lt.1 fun hlt => h.not_gt <| nth_lt_nth_of_lt_card hf hlt hm

theorem nth_injOn (hf : (setOf p).Finite) : (Set.Iio #hf.toFinset).InjOn (nth p) :=
  (nth_strictMonoOn hf).injOn

theorem range_nth_of_finite (hf : (setOf p).Finite) : Set.range (nth p) = insert 0 (setOf p) := by
  simpa only [← List.getD_eq_getElem?_getD, ← nth_eq_getD_sort hf, mem_sort,
    Set.Finite.mem_toFinset] using Set.range_list_getD (hf.toFinset.sort (· ≤ ·)) 0
