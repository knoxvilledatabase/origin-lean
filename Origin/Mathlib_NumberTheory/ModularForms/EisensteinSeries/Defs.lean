/-
Extracted from NumberTheory/ModularForms/EisensteinSeries/Defs.lean
Genuine: 12 of 15 | Dissolved: 3 | Infrastructure: 0
-/
import Origin.Core

/-!
# Eisenstein Series

## Main definitions

* We define Eisenstein series of level `Γ(N)` for any `N : ℕ` and weight `k : ℤ` as the infinite sum
  `∑' v : (Fin 2 → ℤ), (1 / (v 0 * z + v 1) ^ k)`, where `z : ℍ` and `v` ranges over all pairs of
  coprime integers congruent to a fixed pair `(a, b)` modulo `N`. Note that by using `(Fin 2 → ℤ)`
  instead of `ℤ × ℤ` we can state all of the required equivalences using matrices and vectors, which
  makes working with them more convenient.

* We show that they define a slash invariant form of level `Γ(N)` and weight `k`.

## References
* [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005]
-/

noncomputable section

open ModularForm UpperHalfPlane Complex Matrix CongruenceSubgroup Set

open scoped MatrixGroups

namespace EisensteinSeries

variable (N r : ℕ) (a : Fin 2 → ZMod N)

section gammaSet_def

def gammaSet := {v : Fin 2 → ℤ | (↑) ∘ v = a ∧ (v 0).gcd (v 1) = r}

open scoped Function in -- required for scoped `on` notation

lemma pairwise_disjoint_gammaSet : Pairwise (Disjoint on gammaSet N r) := by
  refine fun u v huv ↦ ?_
  contrapose huv
  obtain ⟨f, hf⟩ := Set.not_disjoint_iff.mp huv
  exact hf.1.1.symm.trans hf.2.1

lemma gammaSet_one_const (a a' : Fin 2 → ZMod 1) : gammaSet 1 r a = gammaSet 1 r a' :=
  congr_arg _ (Subsingleton.elim _ _)

lemma gammaSet_one_eq (a : Fin 2 → ZMod 1) :
    gammaSet 1 r a = {v : Fin 2 → ℤ | (v 0).gcd (v 1) = r} := by
  simp [gammaSet, Subsingleton.eq_zero]

lemma gammaSet_one_mem_iff (v : Fin 2 → ℤ) : v ∈ gammaSet 1 r 0 ↔ (v 0).gcd (v 1) = r := by
  simp [gammaSet, Subsingleton.eq_zero]

def gammaSet_one_equiv (a a' : Fin 2 → ZMod 1) : gammaSet 1 r a ≃ gammaSet 1 r a' :=
  Equiv.setCongr (gammaSet_one_const r a a')

abbrev finGcdMap (v : Fin 2 → ℤ) : ℕ := (v 0).gcd (v 1)

-- DISSOLVED: finGcdMap_div

lemma finGcdMap_smul {r : ℕ} (a : ℤ) {v : Fin 2 → ℤ} (hv : finGcdMap v = r) :
    finGcdMap (a • v) = a.natAbs * r := by
  simp [finGcdMap, Int.gcd_mul_left, hv]

abbrev divIntMap (r : ℤ) {m : ℕ} (v : Fin m → ℤ) : Fin m → ℤ := v / r

lemma mem_gammaSet_one (v : Fin 2 → ℤ) : v ∈ gammaSet 1 1 0 ↔ IsCoprime (v 0) (v 1) := by
  rw [gammaSet_one_mem_iff, Int.isCoprime_iff_gcd_eq_one]

lemma gammaSet_div_gcd {r : ℕ} {v : Fin 2 → ℤ} (hv : v ∈ (gammaSet 1 r 0)) (i : Fin 2) :
   (r : ℤ) ∣ v i := by
  fin_cases i <;> simp [← hv.2, Int.gcd_dvd_left, Int.gcd_dvd_right]

-- DISSOLVED: gammaSet_div_gcd_to_gammaSet10_bijection

lemma gammaSet_eq_gcd_mul_divIntMap {r : ℕ} {v : Fin 2 → ℤ} (hv : v ∈ gammaSet 1 r 0) :
    v = r • (divIntMap r v) := by
  by_cases hr : r = 0
  · have hv := hv.2
    simp only [hr, Fin.isValue, Int.gcd_eq_zero_iff, CharP.cast_eq_zero, zero_smul] at *
    ext i
    fin_cases i <;> simp [hv]
  · ext i
    simp_all [Pi.smul_apply, divIntMap, ← Int.mul_ediv_assoc _ (gammaSet_div_gcd hv i)]

-- DISSOLVED: gammaSetDivGcdEquiv
