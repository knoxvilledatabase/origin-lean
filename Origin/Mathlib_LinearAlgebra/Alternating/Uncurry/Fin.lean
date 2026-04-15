/-
Extracted from LinearAlgebra/Alternating/Uncurry/Fin.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Uncurrying alternating maps

Given a function `f` which is linear in the first argument
and is alternating form in the other `n` arguments,
this file defines an alternating form `AlternatingMap.alternatizeUncurryFin f` in `n + 1` arguments.

This function is given by
```
AlternatingMap.alternatizeUncurryFin f v =
  ∑ i : Fin (n + 1), (-1) ^ (i : ℕ) • f (v i) (removeNth i v)
```

Given an alternating map `f` of `n + 1` arguments,
each term in the sum above written for `f.curryLeft` equals the original map,
thus `f.curryLeft.alternatizeUncurryFin = (n + 1) • f`.

We do not multiply the result of `alternatizeUncurryFin` by `(n + 1)⁻¹`
so that the construction works for `R`-multilinear maps over any commutative ring `R`,
not only a field of characteristic zero.

## Main results

- `AlternatingMap.alternatizeUncurryFin_curryLeft`:
  the round-trip formula for currying/uncurrying, see above.

- `AlternatingMap.alternatizeUncurryFin_alternatizeUncurryFinLM_comp_of_symmetric`:
  If `f` is a symmetric bilinear map taking values in the space of alternating maps,
  then the twice uncurried `f` is zero.

A version of the latter theorem for continuous alternating maps
will be used to prove that the second exterior derivative of a differential form is zero.
-/

open Fin Function

namespace AlternatingMap

variable {R : Type*} {M M₂ N N₂ : Type*} [CommRing R] [AddCommGroup M]
  [AddCommGroup M₂] [AddCommGroup N] [AddCommGroup N₂] [Module R M] [Module R M₂]
  [Module R N] [Module R N₂] {n : ℕ}

theorem map_insertNth (f : M [⋀^Fin (n + 1)]→ₗ[R] N) (p : Fin (n + 1)) (x : M) (v : Fin n → M) :
    f (p.insertNth x v) = (-1) ^ (p : ℕ) • f (Matrix.vecCons x v) := by
  rw [← cons_comp_cycleRange, map_perm, Matrix.vecCons]
  simp [Units.smul_def]

theorem neg_one_pow_smul_map_insertNth (f : M [⋀^Fin (n + 1)]→ₗ[R] N) (p : Fin (n + 1)) (x : M)
    (v : Fin n → M) :
    (-1) ^ (p : ℕ) • f (p.insertNth x v) = f (Matrix.vecCons x v) := by
  rw [map_insertNth, smul_smul, ← pow_add, Even.neg_one_pow, one_smul]
  use p

theorem neg_one_pow_smul_map_removeNth_add_eq_zero_of_eq (f : M [⋀^Fin n]→ₗ[R] N)
    {v : Fin (n + 1) → M} {i j : Fin (n + 1)} (hvij : v i = v j) (hij : i ≠ j) :
    (-1) ^ (i : ℕ) • f (i.removeNth v) + (-1) ^ (j : ℕ) • f (j.removeNth v) = 0 := by
  rcases exists_succAbove_eq hij with ⟨i, rfl⟩
  obtain ⟨m, rfl⟩ : ∃ m, m + 1 = n := by simp [i.pos]
  rw [← (i.predAbove j).insertNth_self_removeNth (removeNth _ _), ← removeNth_removeNth_eq_swap,
    removeNth, succAbove_succAbove_predAbove, map_insertNth, ← neg_one_pow_smul_map_insertNth,
    insertNth_removeNth, update_eq_self_iff.2, smul_smul, ← pow_add,
    neg_one_pow_succAbove_add_predAbove, neg_smul, pow_add, mul_smul,
    smul_smul (_ ^ i.val), ← sq, ← pow_mul, pow_mul', neg_one_pow_two, one_pow, one_smul,
    neg_add_cancel]
  exact hvij.symm

def alternatizeUncurryFin (f : M →ₗ[R] M [⋀^Fin n]→ₗ[R] N) :
    M [⋀^Fin (n + 1)]→ₗ[R] N where
  toMultilinearMap :=
    ∑ p : Fin (n + 1), (-1) ^ (p : ℕ) • LinearMap.uncurryMid p (toMultilinearMapLM ∘ₗ f)
  map_eq_zero_of_eq' := by
    intro v i j hvij hij
    suffices ∑ k : Fin (n + 1), (-1) ^ (k : ℕ) • f (v k) (k.removeNth v) = 0 by simpa
    calc
      _ = (-1) ^ (i : ℕ) • f (v i) (i.removeNth v) + (-1) ^ (j : ℕ) • f (v j) (j.removeNth v) := by
        refine Fintype.sum_eq_add _ _ hij fun k ⟨hki, hkj⟩ ↦ ?_
        rcases exists_succAbove_eq hki.symm with ⟨i, rfl⟩
        rcases exists_succAbove_eq hkj.symm with ⟨j, rfl⟩
        rw [(f (v k)).map_eq_zero_of_eq _ hvij (ne_of_apply_ne _ hij), smul_zero]
      _ = 0 := by
        rw [hvij, neg_one_pow_smul_map_removeNth_add_eq_zero_of_eq] <;> assumption
