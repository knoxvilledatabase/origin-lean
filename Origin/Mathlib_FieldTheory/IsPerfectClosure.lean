/-
Extracted from FieldTheory/IsPerfectClosure.lean
Genuine: 12 of 12 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# `IsPerfectClosure` predicate

This file contains `IsPerfectClosure` which asserts that `L` is a perfect closure of `K` under a
ring homomorphism `i : K →+* L`, as well as its basic properties.

## Main definitions

- `pNilradical`: given a natural number `p`, the `p`-nilradical of a ring is defined to be the
  nilradical if `p > 1` (`pNilradical_eq_nilradical`), and defined to be the zero ideal if `p ≤ 1`
  (`pNilradical_eq_bot'`). Equivalently, it is the ideal consisting of elements `x` such that
  `x ^ p ^ n = 0` for some `n` (`mem_pNilradical`).

- `IsPRadical`: a ring homomorphism `i : K →+* L` of characteristic `p` rings is called `p`-radical,
  if or any element `x` of `L` there is `n : ℕ` such that `x ^ (p ^ n)` is contained in `K`,
  and the kernel of `i` is contained in the `p`-nilradical of `K`.
  A generalization of purely inseparable extension for fields.

- `IsPerfectClosure`: if `i : K →+* L` is `p`-radical ring homomorphism, then it makes `L` a
  perfect closure of `K`, if `L` is perfect.

  Our definition makes it synonymous to `IsPRadical` if `PerfectRing L p` is present. A caveat is
  that you need to write `[PerfectRing L p] [IsPerfectClosure i p]`. This is similar to
  `PerfectRing` which has `ExpChar` as a prerequisite.

- `PerfectRing.lift`: if a `p`-radical ring homomorphism `K →+* L` is given, `M` is a perfect ring,
  then any ring homomorphism `K →+* M` can be lifted to `L →+* M`.
  This is similar to `IsAlgClosed.lift` and `IsSepClosed.lift`.

- `PerfectRing.liftEquiv`: `K →+* M` is in one-to-one correspondence with `L →+* M`,
  given by `PerfectRing.lift`. This generalizes `PerfectClosure.lift`.

- `IsPerfectClosure.equiv`: perfect closures of a ring are isomorphic.

## Main results

- `IsPRadical.trans`: composition of `p`-radical ring homomorphisms is also `p`-radical.

- `PerfectClosure.isPRadical`: the absolute perfect closure `PerfectClosure` is a `p`-radical
  extension over the base ring, in particular, it is a perfect closure of the base ring.

- `IsPRadical.isPurelyInseparable`, `IsPurelyInseparable.isPRadical`: `p`-radical and
  purely inseparable are equivalent for fields.

- The (relative) perfect closure `perfectClosure` is a perfect closure
  (inferred from `IsPurelyInseparable.isPRadical` automatically by Lean).

## Tags

perfect ring, perfect closure, purely inseparable

-/

open Module Polynomial IntermediateField Field

noncomputable section

def pNilradical (R : Type*) [CommSemiring R] (p : ℕ) : Ideal R := if 1 < p then nilradical R else ⊥

theorem pNilradical_le_nilradical {R : Type*} [CommSemiring R] {p : ℕ} :
    pNilradical R p ≤ nilradical R := by
  by_cases hp : 1 < p
  · rw [pNilradical, if_pos hp]
  simp_rw [pNilradical, if_neg hp, bot_le]

theorem pNilradical_eq_nilradical {R : Type*} [CommSemiring R] {p : ℕ} (hp : 1 < p) :
    pNilradical R p = nilradical R := by rw [pNilradical, if_pos hp]

theorem pNilradical_eq_bot {R : Type*} [CommSemiring R] {p : ℕ} (hp : ¬ 1 < p) :
    pNilradical R p = ⊥ := by rw [pNilradical, if_neg hp]

theorem pNilradical_eq_bot' {R : Type*} [CommSemiring R] {p : ℕ} (hp : p ≤ 1) :
    pNilradical R p = ⊥ := pNilradical_eq_bot (not_lt.2 hp)

theorem pNilradical_prime {R : Type*} [CommSemiring R] {p : ℕ} (hp : p.Prime) :
    pNilradical R p = nilradical R := pNilradical_eq_nilradical hp.one_lt

theorem pNilradical_one {R : Type*} [CommSemiring R] :
    pNilradical R 1 = ⊥ := pNilradical_eq_bot' rfl.le

theorem mem_pNilradical {R : Type*} [CommSemiring R] {p : ℕ} {x : R} :
    x ∈ pNilradical R p ↔ ∃ n : ℕ, x ^ p ^ n = 0 := by
  by_cases hp : 1 < p
  · rw [pNilradical_eq_nilradical hp]
    refine ⟨fun ⟨n, h⟩ ↦ ⟨n, ?_⟩, fun ⟨n, h⟩ ↦ ⟨p ^ n, h⟩⟩
    rw [← Nat.sub_add_cancel ((n.lt_pow_self hp).le), pow_add, h, mul_zero]
  rw [pNilradical_eq_bot hp, Ideal.mem_bot]
  refine ⟨fun h ↦ ⟨0, by rw [pow_zero, pow_one, h]⟩, fun ⟨n, h⟩ ↦ ?_⟩
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (not_lt.1 hp) with hp | hp
  · by_cases hn : n = 0
    · rwa [hn, pow_zero, pow_one] at h
    rw [hp, zero_pow hn, pow_zero] at h
    subsingleton [subsingleton_of_zero_eq_one h.symm]
  rwa [hp, one_pow, pow_one] at h

theorem sub_mem_pNilradical_iff_pow_expChar_pow_eq {R : Type*} [CommRing R] {p : ℕ} [ExpChar R p]
    {x y : R} : x - y ∈ pNilradical R p ↔ ∃ n : ℕ, x ^ p ^ n = y ^ p ^ n := by
  simp_rw [mem_pNilradical, sub_pow_expChar_pow, sub_eq_zero]

theorem pow_expChar_pow_inj_of_pNilradical_eq_bot (R : Type*) [CommRing R] (p : ℕ) [ExpChar R p]
    (h : pNilradical R p = ⊥) (n : ℕ) : Function.Injective fun x : R ↦ x ^ p ^ n := fun _ _ H ↦
  sub_eq_zero.1 <| Ideal.mem_bot.1 <| h ▸ sub_mem_pNilradical_iff_pow_expChar_pow_eq.2 ⟨n, H⟩

theorem pNilradical_eq_bot_of_frobenius_inj (R : Type*) [CommSemiring R] (p : ℕ) [ExpChar R p]
    (h : Function.Injective (frobenius R p)) : pNilradical R p = ⊥ := bot_unique fun x ↦ by
  rw [mem_pNilradical, Ideal.mem_bot]
  exact fun ⟨n, _⟩ ↦ h.iterate n (by rwa [← coe_iterateFrobenius, map_zero])

theorem PerfectRing.pNilradical_eq_bot (R : Type*) [CommSemiring R] (p : ℕ) [ExpChar R p]
    [PerfectRing R p] : pNilradical R p = ⊥ :=
  pNilradical_eq_bot_of_frobenius_inj R p (injective_frobenius R p)

section IsPerfectClosure

variable {K L M N : Type*}

section CommSemiring

variable [CommSemiring K] [CommSemiring L] [CommSemiring M]
  (i : K →+* L) (j : K →+* M) (f : L →+* M) (p : ℕ)
