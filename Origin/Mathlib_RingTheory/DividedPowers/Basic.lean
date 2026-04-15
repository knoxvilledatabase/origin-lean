/-
Extracted from RingTheory/DividedPowers/Basic.lean
Genuine: 2 of 5 | Dissolved: 1 | Infrastructure: 2
-/
import Origin.Core

/-! # Divided powers

Let `A` be a commutative (semi)ring and `I` be an ideal of `A`.
A *divided power* structure on `I` is the datum of operations `a n ↦ dpow a n`
satisfying relations that model the intuitive formula `dpow n a = a ^ n / n !` and
collected by the structure `DividedPowers`. The list of axioms is embedded in the structure:
To avoid coercions, we rather consider `DividedPowers.dpow : ℕ → A → A`, extended by 0.

* `DividedPowers.dpow_null` asserts that `dpow n x = 0` for `x ∉ I`
* `DividedPowers.dpow_mem` : `dpow n x ∈ I` for `n ≠ 0`

For `x y : A` and `m n : ℕ` such that `x ∈ I` and `y ∈ I`, one has
* `DividedPowers.dpow_zero` : `dpow 0 x = 1`
* `DividedPowers.dpow_one` : `dpow 1 x = 1`
* `DividedPowers.dpow_add` :
  `dpow n (x + y) = (antidiagonal n).sum fun k ↦ dpow k.1 x * dpow k.2 y`,
  this is the binomial theorem without binomial coefficients.
* `DividedPowers.dpow_mul`: `dpow n (a * x) = a ^ n * dpow n x`
* `DividedPowers.mul_dpow` : `dpow m x * dpow n x = choose (m + n) m * dpow (m + n) x`
* `DividedPowers.dpow_comp` : `dpow m (dpow n x) = uniformBell m n * dpow (m * n) x`
* `DividedPowers.dividedPowersBot` : the trivial divided powers structure on the zero ideal
* `DividedPowers.prod_dpow`: a product of divided powers is a multinomial coefficient
  times a divided power
* `DividedPowers.dpow_sum`: the multinomial theorem for divided powers,
  without multinomial coefficients.
* `DividedPowers.ofRingEquiv`: transfer divided powers along `RingEquiv`
* `DividedPowers.equiv`: the equivalence `DividedPowers I ≃ DividedPowers J`,
  for `e : R ≃+* S`, and `I : Ideal R`, `J : Ideal S` such that `I.map e = J`
* `DividedPowers.exp`: the power series `Σ (dpow n a) X ^n`
* `DividedPowers.exp_add`: its multiplicativity

## References

* [P. Berthelot (1974), *Cohomologie cristalline des schémas de
  caractéristique $p$ > 0*][Berthelot-1974]

* [P. Berthelot and A. Ogus (1978), *Notes on crystalline
  cohomology*][BerthelotOgus-1978]

* [N. Roby (1963), *Lois polynomes et lois formelles en théorie des
  modules*][Roby-1963]

* [N. Roby (1965), *Les algèbres à puissances dividées*][Roby-1965]

## Discussion

* In practice, one often has a single such structure to handle on a given ideal,
  but several ideals of the same ring might be considered.
  Without any explicit mention of the ideal, it is not clear whether such structures
  should be provided as instances.

* We do not provide any notation such as `a ^[n]` for `dpow a n`.

-/

open Finset Nat Ideal

section DividedPowersDefinition

variable {A : Type*} [CommSemiring A] (I : Ideal A)

-- DISSOLVED: DividedPowers

variable (A) in

noncomputable def dividedPowersBot : DividedPowers (⊥ : Ideal A) where
  dpow n a := open Classical in ite (a = 0 ∧ n = 0) 1 0
  dpow_null {n a} ha := by
    simp only [mem_bot] at ha
    rw [if_neg]
    exact not_and_of_not_left (n = 0) ha
  dpow_zero ha := by
    rw [mem_bot.mp ha]
    simp only [and_self, ite_true]
  dpow_one ha := by
    simp [mem_bot.mp ha]
  dpow_mem {n a} hn _ := by
    simp only [mem_bot, ite_eq_right_iff, and_imp]
    exact fun _ a ↦ False.elim (hn a)
  dpow_add ha hb := by
    rw [mem_bot.mp ha, mem_bot.mp hb, add_zero]
    simp only [true_and, mul_ite, mul_one, mul_zero]
    split_ifs with h
    · simp [h]
    · symm
      apply sum_eq_zero
      grind [mem_antidiagonal]
  dpow_mul {n} _ _ hx := by
    rw [mem_bot.mp hx]
    simp only [mul_zero, true_and, mul_ite, mul_one]
    by_cases hn : n = 0
    · rw [if_pos hn, hn, if_pos rfl, _root_.pow_zero]
    · simp only [if_neg hn]
  mul_dpow {m n x} hx := by
    rw [mem_bot.mp hx]
    simp only [true_and, mul_ite, mul_one, mul_zero, add_eq_zero]
    by_cases hn : n = 0
    · simp only [hn, ite_true, and_true, add_zero, choose_self, cast_one]
    · rw [if_neg hn, if_neg]
      exact not_and_of_not_right (m = 0) hn
  dpow_comp m {n a} hn ha := by
    rw [mem_bot.mp ha]
    simp only [true_and, ite_eq_right_iff, _root_.mul_eq_zero, mul_ite, mul_one, mul_zero]
    by_cases hm : m = 0
    · simp [hm, uniformBell_zero_left, hn]
    · simp only [hm, and_false, ite_false, false_or, if_neg hn]

lemma dividedPowersBot_dpow_eq [DecidableEq A] (n : ℕ) (a : A) :
    (dividedPowersBot A).dpow n a =
      if a = 0 ∧ n = 0 then 1 else 0 := by
  simp [dividedPowersBot]

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

variable {I} in
