/-
Extracted from Data/Finsupp/Fin.lean
Genuine: 8 of 13 | Dissolved: 3 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.Data.Finsupp.Defs

/-!
# `cons` and `tail` for maps `Fin n →₀ M`

We interpret maps `Fin n →₀ M` as `n`-tuples of elements of `M`,
We define the following operations:
* `Finsupp.tail` : the tail of a map `Fin (n + 1) →₀ M`, i.e., its last `n` entries;
* `Finsupp.cons` : adding an element at the beginning of an `n`-tuple, to get an `n + 1`-tuple;

In this context, we prove some usual properties of `tail` and `cons`, analogous to those of
`Data.Fin.Tuple.Basic`.
-/

open Function

noncomputable section

namespace Finsupp

variable {n : ℕ} (i : Fin n) {M : Type*} [Zero M] (y : M) (t : Fin (n + 1) →₀ M) (s : Fin n →₀ M)

def tail (s : Fin (n + 1) →₀ M) : Fin n →₀ M :=
  Finsupp.equivFunOnFinite.symm (Fin.tail s)

def cons (y : M) (s : Fin n →₀ M) : Fin (n + 1) →₀ M :=
  Finsupp.equivFunOnFinite.symm (Fin.cons y s : Fin (n + 1) → M)

theorem tail_apply : tail t i = t i.succ :=
  rfl

@[simp]
theorem cons_zero : cons y s 0 = y :=
  rfl

@[simp]
theorem cons_succ : cons y s i.succ = s i :=
  -- Porting note: was Fin.cons_succ _ _ _
  rfl

@[simp]
theorem tail_cons : tail (cons y s) = s :=
  ext fun k => by simp only [tail_apply, cons_succ]

@[simp]
theorem cons_tail : cons (t 0) (tail t) = t := by
  ext a
  by_cases c_a : a = 0
  · rw [c_a, cons_zero]
  · rw [← Fin.succ_pred a c_a, cons_succ, ← tail_apply]

@[simp]
theorem cons_zero_zero : cons 0 (0 : Fin n →₀ M) = 0 := by
  ext a
  by_cases c : a = 0
  · simp [c]
  · rw [← Fin.succ_pred a c, cons_succ]
    simp

variable {s} {y}

-- DISSOLVED: cons_ne_zero_of_left

-- DISSOLVED: cons_ne_zero_of_right

-- DISSOLVED: cons_ne_zero_iff

lemma cons_support : (s.cons y).support ⊆ insert 0 (s.support.map (Fin.succEmb n)) := by
  intro i hi
  suffices i = 0 ∨ ∃ a, ¬s a = 0 ∧ a.succ = i by simpa
  apply (Fin.eq_zero_or_eq_succ i).imp id (Exists.imp _)
  rintro i rfl
  simpa [Finsupp.mem_support_iff] using hi

lemma cons_right_injective {n : ℕ} {M : Type*} [Zero M] (y : M) :
    Injective (Finsupp.cons y : (Fin n →₀ M) → Fin (n + 1) →₀ M) :=
  (equivFunOnFinite.symm.injective.comp ((Fin.cons_right_injective _).comp DFunLike.coe_injective))

end Finsupp
