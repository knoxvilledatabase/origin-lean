/-
Extracted from RingTheory/ChainOfDivisors.lean
Genuine: 6 | Conflates: 0 | Dissolved: 14 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Order.Atoms
import Mathlib.Order.Hom.Bounded

/-!

# Chains of divisors

The results in this file show that in the monoid `Associates M` of a `UniqueFactorizationMonoid`
`M`, an element `a` is an n-th prime power iff its set of divisors is a strictly increasing chain
of length `n + 1`, meaning that we can find a strictly increasing bijection between `Fin (n + 1)`
and the set of factors of `a`.

## Main results
- `DivisorChain.exists_chain_of_prime_pow` : existence of a chain for prime powers.
- `DivisorChain.is_prime_pow_of_has_chain` : elements that have a chain are prime powers.
- `multiplicity_prime_eq_multiplicity_image_by_factor_orderIso` : if there is a
  monotone bijection `d` between the set of factors of `a : Associates M` and the set of factors of
  `b : Associates N` then for any prime `p ∣ a`, `multiplicity p a = multiplicity (d p) b`.
- `multiplicity_eq_multiplicity_factor_dvd_iso_of_mem_normalizedFactors` : if there is a bijection
  between the set of factors of `a : M` and `b : N` then for any prime `p ∣ a`,
  `multiplicity p a = multiplicity (d p) b`


## TODO
- Create a structure for chains of divisors.
- Simplify proof of `mem_normalizedFactors_factor_dvd_iso_of_mem_normalizedFactors` using
  `mem_normalizedFactors_factor_order_iso_of_mem_normalizedFactors` or vice versa.

-/

variable {M : Type*} [CancelCommMonoidWithZero M]

-- DISSOLVED: Associates.isAtom_iff

open UniqueFactorizationMonoid multiplicity Irreducible Associates

namespace DivisorChain

-- DISSOLVED: exists_chain_of_prime_pow

-- DISSOLVED: element_of_chain_not_isUnit_of_index_ne_zero

theorem first_of_chain_isUnit {q : Associates M} {n : ℕ} {c : Fin (n + 1) → Associates M}
    (h₁ : StrictMono c) (h₂ : ∀ {r}, r ≤ q ↔ ∃ i, r = c i) : IsUnit (c 0) := by
  obtain ⟨i, hr⟩ := h₂.mp Associates.one_le
  rw [Associates.isUnit_iff_eq_one, ← Associates.le_one_iff, hr]
  exact h₁.monotone (Fin.zero_le i)

-- DISSOLVED: second_of_chain_is_irreducible

-- DISSOLVED: eq_second_of_chain_of_prime_dvd

theorem card_subset_divisors_le_length_of_chain {q : Associates M} {n : ℕ}
    {c : Fin (n + 1) → Associates M} (h₂ : ∀ {r}, r ≤ q ↔ ∃ i, r = c i) {m : Finset (Associates M)}
    (hm : ∀ r, r ∈ m → r ≤ q) : m.card ≤ n + 1 := by
  classical
    have mem_image : ∀ r : Associates M, r ≤ q → r ∈ Finset.univ.image c := by
      intro r hr
      obtain ⟨i, hi⟩ := h₂.1 hr
      exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi.symm⟩
    rw [← Finset.card_fin (n + 1)]
    exact (Finset.card_le_card fun x hx => mem_image x <| hm x hx).trans Finset.card_image_le

variable [UniqueFactorizationMonoid M]

-- DISSOLVED: element_of_chain_eq_pow_second_of_chain

-- DISSOLVED: eq_pow_second_of_chain_of_has_chain

-- DISSOLVED: isPrimePow_of_has_chain

end DivisorChain

variable {N : Type*} [CancelCommMonoidWithZero N]

theorem factor_orderIso_map_one_eq_bot {m : Associates M} {n : Associates N}
    (d : { l : Associates M // l ≤ m } ≃o { l : Associates N // l ≤ n }) :
    (d ⟨1, one_dvd m⟩ : Associates N) = 1 := by
  letI : OrderBot { l : Associates M // l ≤ m } := Subtype.orderBot bot_le
  letI : OrderBot { l : Associates N // l ≤ n } := Subtype.orderBot bot_le
  simp only [← Associates.bot_eq_one, Subtype.mk_bot, bot_le, Subtype.coe_eq_bot_iff]
  letI : BotHomClass ({ l // l ≤ m } ≃o { l // l ≤ n }) _ _ := OrderIsoClass.toBotHomClass
  exact map_bot d

theorem coe_factor_orderIso_map_eq_one_iff {m u : Associates M} {n : Associates N} (hu' : u ≤ m)
    (d : Set.Iic m ≃o Set.Iic n) : (d ⟨u, hu'⟩ : Associates N) = 1 ↔ u = 1 :=
  ⟨fun hu => by
    rw [show u = (d.symm ⟨d ⟨u, hu'⟩, (d ⟨u, hu'⟩).prop⟩) by
        simp only [Subtype.coe_eta, OrderIso.symm_apply_apply, Subtype.coe_mk]]
    conv_rhs => rw [← factor_orderIso_map_one_eq_bot d.symm]
    congr, fun hu => by
    simp_rw [hu]
    conv_rhs => rw [← factor_orderIso_map_one_eq_bot d]
    rfl⟩

section

variable [UniqueFactorizationMonoid N] [UniqueFactorizationMonoid M]

open DivisorChain

-- DISSOLVED: pow_image_of_prime_by_factor_orderIso_dvd

-- DISSOLVED: map_prime_of_factor_orderIso

-- DISSOLVED: mem_normalizedFactors_factor_orderIso_of_mem_normalizedFactors

theorem emultiplicity_prime_le_emultiplicity_image_by_factor_orderIso {m p : Associates M}
    {n : Associates N} (hp : p ∈ normalizedFactors m) (d : Set.Iic m ≃o Set.Iic n) :
    emultiplicity p m ≤ emultiplicity (↑(d ⟨p, dvd_of_mem_normalizedFactors hp⟩)) n := by
  by_cases hn : n = 0
  · simp [hn]
  by_cases hm : m = 0
  · simp [hm] at hp
  rw [(finite_prime_left (prime_of_normalized_factor p hp) hm).emultiplicity_eq_multiplicity,
    ← pow_dvd_iff_le_emultiplicity]
  apply pow_image_of_prime_by_factor_orderIso_dvd hn hp d (pow_multiplicity_dvd ..)

-- DISSOLVED: emultiplicity_prime_eq_emultiplicity_image_by_factor_orderIso

end

variable [Subsingleton Mˣ] [Subsingleton Nˣ]

@[simps]
def mkFactorOrderIsoOfFactorDvdEquiv {m : M} {n : N} {d : { l : M // l ∣ m } ≃ { l : N // l ∣ n }}
    (hd : ∀ l l', (d l : N) ∣ d l' ↔ (l : M) ∣ (l' : M)) :
    Set.Iic (Associates.mk m) ≃o Set.Iic (Associates.mk n) where
  toFun l :=
    ⟨Associates.mk
        (d
          ⟨associatesEquivOfUniqueUnits ↑l, by
            obtain ⟨x, hx⟩ := l
            rw [Subtype.coe_mk, associatesEquivOfUniqueUnits_apply, out_dvd_iff]
            exact hx⟩),
      mk_le_mk_iff_dvd.mpr (Subtype.prop (d ⟨associatesEquivOfUniqueUnits ↑l, _⟩))⟩
  invFun l :=
    ⟨Associates.mk
        (d.symm
          ⟨associatesEquivOfUniqueUnits ↑l, by
            obtain ⟨x, hx⟩ := l
            rw [Subtype.coe_mk, associatesEquivOfUniqueUnits_apply, out_dvd_iff]
            exact hx⟩),
      mk_le_mk_iff_dvd.mpr (Subtype.prop (d.symm ⟨associatesEquivOfUniqueUnits ↑l, _⟩))⟩
  left_inv := fun ⟨l, hl⟩ => by
    simp only [Subtype.coe_eta, Equiv.symm_apply_apply, Subtype.coe_mk,
      associatesEquivOfUniqueUnits_apply, mk_out, out_mk, normalize_eq]
  right_inv := fun ⟨l, hl⟩ => by
    simp only [Subtype.coe_eta, Equiv.apply_symm_apply, Subtype.coe_mk,
      associatesEquivOfUniqueUnits_apply, out_mk, normalize_eq, mk_out]
  map_rel_iff' := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    simp only [Equiv.coe_fn_mk, Subtype.mk_le_mk, Associates.mk_le_mk_iff_dvd, hd,
        Subtype.coe_mk, associatesEquivOfUniqueUnits_apply, out_dvd_iff, mk_out]

variable [UniqueFactorizationMonoid M] [UniqueFactorizationMonoid N]

-- DISSOLVED: mem_normalizedFactors_factor_dvd_iso_of_mem_normalizedFactors

-- DISSOLVED: emultiplicity_factor_dvd_iso_eq_emultiplicity_of_mem_normalizedFactors
