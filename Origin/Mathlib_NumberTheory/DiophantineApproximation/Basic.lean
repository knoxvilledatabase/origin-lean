/-
Extracted from NumberTheory/DiophantineApproximation/Basic.lean
Genuine: 9 of 9 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Diophantine Approximation

The first part of this file gives proofs of various versions of
**Dirichlet's approximation theorem** and its important consequence that when $\xi$ is an
irrational real number, then there are infinitely many rationals $x/y$ (in lowest terms)
such that
$$\left|\xi - \frac{x}{y}\right| < \frac{1}{y^2} \,.$$
The proof is based on the pigeonhole principle.

The second part of the file gives a proof of **Legendre's Theorem** on rational approximation,
which states that if $\xi$ is a real number and $x/y$ is a rational number such that
$$\left|\xi - \frac{x}{y}\right| < \frac{1}{2y^2} \,,$$
then $x/y$ must be a convergent of the continued fraction expansion of $\xi$.

## Main statements

The main results are three variants of Dirichlet's approximation theorem:
* `Real.exists_int_int_abs_mul_sub_le`, which states that for all real `ξ` and natural `0 < n`,
  there are integers `j` and `k` with `0 < k ≤ n` and `|k*ξ - j| ≤ 1/(n+1)`,
* `Real.exists_nat_abs_mul_sub_round_le`, which replaces `j` by `round(k*ξ)` and uses
  a natural number `k`,
* `Real.exists_rat_abs_sub_le_and_den_le`, which says that there is a rational number `q`
  satisfying `|ξ - q| ≤ 1/((n+1)*q.den)` and `q.den ≤ n`,

and
* `Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational`, which states that
  for irrational `ξ`, the set `{q : ℚ | |ξ - q| < 1/q.den^2}` is infinite.

We also show a converse,
* `Rat.finite_rat_abs_sub_lt_one_div_den_sq`, which states that the set above is finite
  when `ξ` is a rational number.

Both statements are combined to give an equivalence,
`Real.infinite_rat_abs_sub_lt_one_div_den_sq_iff_irrational`.

There are two versions of Legendre's Theorem. One, `Real.exists_rat_eq_convergent`, uses
`Real.convergent`, a simple recursive definition of the convergents that is also defined
in this file, whereas the other, `Real.exists_convs_eq_rat` defined in the file
`Mathlib/NumberTheory/DiophantineApproximation/ContinuedFractions.lean`, uses
`GenContFract.convs` of `GenContFract.of ξ`.

## Implementation notes

We use the namespace `Real` for the results on real numbers and `Rat` for the results
on rational numbers. We introduce a secondary namespace `real.contfrac_legendre`
to separate off a definition and some technical auxiliary lemmas used in the proof
of Legendre's Theorem. For remarks on the proof of Legendre's Theorem, see below.

## References

<https://en.wikipedia.org/wiki/Dirichlet%27s_approximation_theorem>
<https://de.wikipedia.org/wiki/Kettenbruch> (The German Wikipedia page on continued
fractions is much more extensive than the English one.)

## Tags

Diophantine approximation, Dirichlet's approximation theorem, continued fraction
-/

namespace Real

section Dirichlet

/-!
### Dirichlet's approximation theorem

We show that for any real number `ξ` and positive natural `n`, there is a fraction `q`
such that `q.den ≤ n` and `|ξ - q| ≤ 1/((n+1)*q.den)`.
-/

open Finset Int

theorem exists_int_int_abs_mul_sub_le (ξ : ℝ) {n : ℕ} (n_pos : 0 < n) :
    ∃ j k : ℤ, 0 < k ∧ k ≤ n ∧ |↑k * ξ - j| ≤ 1 / (n + 1) := by
  let f : ℤ → ℤ := fun m => ⌊fract (ξ * m) * (n + 1)⌋
  have hn : 0 < (n : ℝ) + 1 := mod_cast Nat.succ_pos _
  have hfu := fun m : ℤ => mul_lt_of_lt_one_left hn <| fract_lt_one (ξ * ↑m)
  conv in |_| ≤ _ => rw [mul_comm, le_div_iff₀ hn, ← abs_of_pos hn, ← abs_mul]
  let D := Icc (0 : ℤ) n
  by_cases! H : ∃ m ∈ D, f m = n
  · obtain ⟨m, hm, hf⟩ := H
    have hf' : ((n : ℤ) : ℝ) ≤ fract (ξ * m) * (n + 1) := hf ▸ floor_le (fract (ξ * m) * (n + 1))
    have hm₀ : 0 < m := by
      have hf₀ : f 0 = 0 := by
        simp only [f, cast_zero, mul_zero, fract_zero, zero_mul, floor_zero]
      refine Ne.lt_of_le (fun h => n_pos.ne ?_) (mem_Icc.mp hm).1
      exact mod_cast hf₀.symm.trans (h.symm ▸ hf : f 0 = n)
    refine ⟨⌊ξ * m⌋ + 1, m, hm₀, (mem_Icc.mp hm).2, ?_⟩
    rw [cast_add, ← sub_sub, sub_mul, cast_one, one_mul, abs_le]
    refine
      ⟨le_sub_iff_add_le.mpr ?_, sub_le_iff_le_add.mpr <| le_of_lt <| (hfu m).trans <| lt_one_add _⟩
    simpa only [neg_add_cancel_comm_assoc] using hf'
  · have hD : #(Ico (0 : ℤ) n) < #D := by rw [card_Icc, card_Ico]; exact lt_add_one n
    have hfu' : ∀ m, f m ≤ n := fun m => lt_add_one_iff.mp (floor_lt.mpr (mod_cast hfu m))
    have hwd : ∀ m : ℤ, m ∈ D → f m ∈ Ico (0 : ℤ) n := fun x hx =>
      mem_Ico.mpr
        ⟨floor_nonneg.mpr (mul_nonneg (fract_nonneg (ξ * x)) hn.le), Ne.lt_of_le (H x hx) (hfu' x)⟩
    obtain ⟨x, hx, y, hy, x_lt_y, hxy⟩ : ∃ x ∈ D, ∃ y ∈ D, x < y ∧ f x = f y := by
      obtain ⟨x, hx, y, hy, x_ne_y, hxy⟩ := exists_ne_map_eq_of_card_lt_of_maps_to hD hwd
      rcases lt_trichotomy x y with (h | h | h)
      exacts [⟨x, hx, y, hy, h, hxy⟩, False.elim (x_ne_y h), ⟨y, hy, x, hx, h, hxy.symm⟩]
    refine
      ⟨⌊ξ * y⌋ - ⌊ξ * x⌋, y - x, sub_pos_of_lt x_lt_y,
        sub_le_iff_le_add.mpr <| le_add_of_le_of_nonneg (mem_Icc.mp hy).2 (mem_Icc.mp hx).1, ?_⟩
    convert_to |fract (ξ * y) * (n + 1) - fract (ξ * x) * (n + 1)| ≤ 1
    · congr; push_cast; simp only [fract]; ring
    exact (abs_sub_lt_one_of_floor_eq_floor hxy.symm).le

theorem exists_nat_abs_mul_sub_round_le (ξ : ℝ) {n : ℕ} (n_pos : 0 < n) :
    ∃ k : ℕ, 0 < k ∧ k ≤ n ∧ |↑k * ξ - round (↑k * ξ)| ≤ 1 / (n + 1) := by
  obtain ⟨j, k, hk₀, hk₁, h⟩ := exists_int_int_abs_mul_sub_le ξ n_pos
  have hk := toNat_of_nonneg hk₀.le
  rw [← hk] at hk₀ hk₁ h
  exact ⟨k.toNat, natCast_pos.mp hk₀, Nat.cast_le.mp hk₁, (round_le (↑k.toNat * ξ) j).trans h⟩

theorem exists_rat_abs_sub_le_and_den_le (ξ : ℝ) {n : ℕ} (n_pos : 0 < n) :
    ∃ q : ℚ, |ξ - q| ≤ 1 / ((n + 1) * q.den) ∧ q.den ≤ n := by
  obtain ⟨j, k, hk₀, hk₁, h⟩ := exists_int_int_abs_mul_sub_le ξ n_pos
  have hk₀' : (0 : ℝ) < k := Int.cast_pos.mpr hk₀
  have hden : ((j / k : ℚ).den : ℤ) ≤ k := by
    convert le_of_dvd hk₀ (Rat.den_dvd j k)
    exact Rat.intCast_div_eq_divInt _ _
  refine ⟨j / k, ?_, Nat.cast_le.mp (hden.trans hk₁)⟩
  rw [← div_div, le_div_iff₀ (Nat.cast_pos.mpr <| Rat.pos _ : (0 : ℝ) < _)]
  refine (mul_le_mul_of_nonneg_left (Int.cast_le.mpr hden : _ ≤ (k : ℝ)) (abs_nonneg _)).trans ?_
  rwa [← abs_of_pos hk₀', Rat.cast_div, Rat.cast_intCast, Rat.cast_intCast, ← abs_mul, sub_mul,
    div_mul_cancel₀ _ hk₀'.ne', mul_comm]

end Dirichlet

section RatApprox

/-!
### Infinitely many good approximations to irrational numbers

We show that an irrational real number `ξ` has infinitely many "good rational approximations",
i.e., fractions `x/y` in lowest terms such that `|ξ - x/y| < 1/y^2`.
-/

open Set

theorem exists_rat_abs_sub_lt_and_lt_of_irrational {ξ : ℝ} (hξ : Irrational ξ) (q : ℚ) :
    ∃ q' : ℚ, |ξ - q'| < 1 / (q'.den : ℝ) ^ 2 ∧ |ξ - q'| < |ξ - q| := by
  have h := abs_pos.mpr (sub_ne_zero.mpr <| Irrational.ne_rat hξ q)
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / |ξ - q|)
  have m_pos : (0 : ℝ) < m := (one_div_pos.mpr h).trans hm
  obtain ⟨q', hbd, hden⟩ := exists_rat_abs_sub_le_and_den_le ξ (Nat.cast_pos.mp m_pos)
  have den_pos : (0 : ℝ) < q'.den := Nat.cast_pos.mpr q'.pos
  have md_pos := mul_pos (add_pos m_pos zero_lt_one) den_pos
  refine
    ⟨q', lt_of_le_of_lt hbd ?_,
      lt_of_le_of_lt hbd <|
        (one_div_lt md_pos h).mpr <|
          hm.trans <|
            lt_of_lt_of_le (lt_add_one _) <|
              (le_mul_iff_one_le_right <| add_pos m_pos zero_lt_one).mpr <|
                mod_cast (q'.pos : 1 ≤ q'.den)⟩
  rw [sq, one_div_lt_one_div md_pos (mul_pos den_pos den_pos), mul_lt_mul_iff_left₀ den_pos]
  exact lt_add_of_le_of_pos (Nat.cast_le.mpr hden) zero_lt_one

theorem infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational {ξ : ℝ} (hξ : Irrational ξ) :
    {q : ℚ | |ξ - q| < 1 / (q.den : ℝ) ^ 2}.Infinite := by
  refine Or.resolve_left (Set.finite_or_infinite _) fun h => ?_
  obtain ⟨q, _, hq⟩ :=
    exists_min_image {q : ℚ | |ξ - q| < 1 / (q.den : ℝ) ^ 2} (fun q => |ξ - q|) h
      ⟨⌊ξ⌋, by simp [abs_of_nonneg, Int.fract_lt_one]⟩
  obtain ⟨q', hmem, hbetter⟩ := exists_rat_abs_sub_lt_and_lt_of_irrational hξ q
  exact lt_irrefl _ (lt_of_le_of_lt (hq q' hmem) hbetter)

end RatApprox

end Real

namespace Rat

/-!
### Finitely many good approximations to rational numbers

We now show that a rational number `ξ` has only finitely many good rational
approximations.
-/

open Set

theorem den_le_and_le_num_le_of_sub_lt_one_div_den_sq {ξ q : ℚ}
    (h : |ξ - q| < 1 / (q.den : ℚ) ^ 2) :
    q.den ≤ ξ.den ∧ ⌈ξ * q.den⌉ - 1 ≤ q.num ∧ q.num ≤ ⌊ξ * q.den⌋ + 1 := by
  have hq₀ : (0 : ℚ) < q.den := Nat.cast_pos.mpr q.pos
  replace h : |ξ * q.den - q.num| < 1 / q.den := by
    rw [← mul_lt_mul_iff_left₀ hq₀] at h
    conv_lhs at h => rw [← abs_of_pos hq₀, ← abs_mul, sub_mul, mul_den_eq_num]
    rwa [sq, div_mul, mul_div_cancel_left₀ _ hq₀.ne'] at h
  constructor
  · rcases eq_or_ne ξ q with (rfl | H)
    · exact le_rfl
    · have hξ₀ : (0 : ℚ) < ξ.den := Nat.cast_pos.mpr ξ.pos
      rw [← Rat.num_div_den ξ, div_mul_eq_mul_div, div_sub' hξ₀.ne', abs_div, abs_of_pos hξ₀,
        div_lt_iff₀ hξ₀, div_mul_comm, mul_one] at h
      refine Nat.cast_le.mp ((one_lt_div hq₀).mp <| lt_of_le_of_lt ?_ h).le
      norm_cast
      rw [mul_comm _ q.num]
      exact Int.one_le_abs (sub_ne_zero_of_ne <| mt Rat.eq_iff_mul_eq_mul.mpr H)
  · obtain ⟨h₁, h₂⟩ :=
      abs_sub_lt_iff.mp
        (h.trans_le <|
          (one_div_le zero_lt_one hq₀).mp <| (@one_div_one ℚ _).symm ▸ Nat.cast_le.mpr q.pos)
    rw [sub_lt_iff_lt_add, add_comm] at h₁ h₂
    rw [← sub_lt_iff_lt_add] at h₂
    norm_cast at h₁ h₂
    exact
      ⟨sub_le_iff_le_add.mpr (Int.ceil_le.mpr h₁.le), sub_le_iff_le_add.mp (Int.le_floor.mpr h₂.le)⟩

theorem finite_rat_abs_sub_lt_one_div_den_sq (ξ : ℚ) :
    {q : ℚ | |ξ - q| < 1 / (q.den : ℚ) ^ 2}.Finite := by
  let f : ℚ → ℤ × ℕ := fun q => (q.num, q.den)
  set s := {q : ℚ | |ξ - q| < 1 / (q.den : ℚ) ^ 2}
  have hinj : Function.Injective f := by
    intro a b hab
    simp only [f, Prod.mk_inj] at hab
    rw [← Rat.num_div_den a, ← Rat.num_div_den b, hab.1, hab.2]
  have H : f '' s ⊆ ⋃ (y : ℕ) (_ : y ∈ Ioc 0 ξ.den), Icc (⌈ξ * y⌉ - 1) (⌊ξ * y⌋ + 1) ×ˢ {y} := by
    intro xy hxy
    simp only [mem_image] at hxy
    obtain ⟨q, hq₁, hq₂⟩ := hxy
    obtain ⟨hd, hn⟩ := den_le_and_le_num_le_of_sub_lt_one_div_den_sq hq₁
    simp_rw [mem_iUnion]
    refine ⟨q.den, Set.mem_Ioc.mpr ⟨q.pos, hd⟩, ?_⟩
    simp only [prod_singleton, mem_image, mem_Icc]
    exact ⟨q.num, hn, hq₂⟩
  refine (Finite.subset ?_ H).of_finite_image hinj.injOn
  exact Finite.biUnion (finite_Ioc _ _) fun x _ => Finite.prod (finite_Icc _ _) (finite_singleton _)

end Rat

theorem Real.infinite_rat_abs_sub_lt_one_div_den_sq_iff_irrational (ξ : ℝ) :
    {q : ℚ | |ξ - q| < 1 / (q.den : ℝ) ^ 2}.Infinite ↔ Irrational ξ := by
  refine
    ⟨fun h => (irrational_iff_ne_rational ξ).mpr fun a b _ => ?_,
      Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational⟩
  contrapose! h
  convert Rat.finite_rat_abs_sub_lt_one_div_den_sq ((a : ℚ) / b) with q
  rw [h, (by (push_cast; rfl) : (1 : ℝ) / (q.den : ℝ) ^ 2 = (1 / (q.den : ℚ) ^ 2 : ℚ))]
  norm_cast

/-!
### Legendre's Theorem on Rational Approximation

We prove **Legendre's Theorem** on rational approximation: If $\xi$ is a real number and
$x/y$ is a rational number such that $|\xi - x/y| < 1/(2y^2)$,
then $x/y$ is a convergent of the continued fraction expansion of $\xi$.

The proof is by induction. However, the induction proof does not work with the
statement as given, since the assumption is too weak to imply the corresponding
statement for the application of the induction hypothesis. This can be remedied
by making the statement slightly stronger. Namely, we assume that $|\xi - x/y| < 1/(y(2y-1))$
when $y \ge 2$ and $-\frac{1}{2} < \xi - x < 1$ when $y = 1$.
-/

section Convergent

namespace Real

open Int

/-!
### Convergents: definition and API lemmas
-/

noncomputable def convergent : ℝ → ℕ → ℚ
  | ξ, 0 => ⌊ξ⌋
  | ξ, n + 1 => ⌊ξ⌋ + (convergent (fract ξ)⁻¹ n)⁻¹
