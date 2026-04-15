/-
Extracted from RingTheory/UniqueFactorizationDomain/NormalizedFactors.lean
Genuine: 20 | Conflates: 0 | Dissolved: 10 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

/-!
# Unique factorization and normalization

## Main definitions
* `UniqueFactorizationMonoid.normalizedFactors`: choose a multiset of prime factors that are unique
  by normalizing them.
* `UniqueFactorizationMonoid.normalizationMonoid`: choose a way of normalizing the elements of a UFM
-/

variable {α : Type*}

local infixl:50 " ~ᵤ " => Associated

namespace UniqueFactorizationMonoid

variable [CancelCommMonoidWithZero α] [NormalizationMonoid α]

variable [UniqueFactorizationMonoid α]

noncomputable def normalizedFactors (a : α) : Multiset α :=
  Multiset.map normalize <| factors a

@[simp]
theorem factors_eq_normalizedFactors {M : Type*} [CancelCommMonoidWithZero M]
    [UniqueFactorizationMonoid M] [Subsingleton Mˣ] (x : M) : factors x = normalizedFactors x := by
  unfold normalizedFactors
  convert (Multiset.map_id (factors x)).symm
  ext p
  exact normalize_eq p

-- DISSOLVED: normalizedFactors_prod

theorem prime_of_normalized_factor {a : α} : ∀ x : α, x ∈ normalizedFactors a → Prime x := by
  rw [normalizedFactors, factors]
  split_ifs with ane0; · simp
  intro x hx; rcases Multiset.mem_map.1 hx with ⟨y, ⟨hy, rfl⟩⟩
  rw [(normalize_associated _).prime_iff]
  exact (Classical.choose_spec (UniqueFactorizationMonoid.exists_prime_factors a ane0)).1 y hy

theorem irreducible_of_normalized_factor {a : α} :
    ∀ x : α, x ∈ normalizedFactors a → Irreducible x := fun x h =>
  (prime_of_normalized_factor x h).irreducible

theorem normalize_normalized_factor {a : α} :
    ∀ x : α, x ∈ normalizedFactors a → normalize x = x := by
  rw [normalizedFactors, factors]
  split_ifs with h; · simp
  intro x hx
  obtain ⟨y, _, rfl⟩ := Multiset.mem_map.1 hx
  apply normalize_idem

theorem normalizedFactors_irreducible {a : α} (ha : Irreducible a) :
    normalizedFactors a = {normalize a} := by
  obtain ⟨p, a_assoc, hp⟩ :=
    prime_factors_irreducible ha ⟨prime_of_normalized_factor, normalizedFactors_prod ha.ne_zero⟩
  have p_mem : p ∈ normalizedFactors a := by
    rw [hp]
    exact Multiset.mem_singleton_self _
  convert hp
  rwa [← normalize_normalized_factor p p_mem, normalize_eq_normalize_iff, dvd_dvd_iff_associated]

theorem normalizedFactors_eq_of_dvd (a : α) :
    ∀ᵉ (p ∈ normalizedFactors a) (q ∈ normalizedFactors a), p ∣ q → p = q := by
  intro p hp q hq hdvd
  convert normalize_eq_normalize hdvd
          ((prime_of_normalized_factor _ hp).irreducible.dvd_symm
            (prime_of_normalized_factor _ hq).irreducible hdvd) <;>
    apply (normalize_normalized_factor _ ‹_›).symm

-- DISSOLVED: exists_mem_normalizedFactors_of_dvd

-- DISSOLVED: exists_mem_normalizedFactors

@[simp]
theorem normalizedFactors_zero : normalizedFactors (0 : α) = 0 := by
  simp [normalizedFactors, factors]

@[simp]
theorem normalizedFactors_one : normalizedFactors (1 : α) = 0 := by
  cases' subsingleton_or_nontrivial α with h h
  · dsimp [normalizedFactors, factors]
    simp [Subsingleton.elim (1 : α) 0]
  · rw [← Multiset.rel_zero_right]
    apply factors_unique irreducible_of_normalized_factor
    · intro x hx
      exfalso
      apply Multiset.not_mem_zero x hx
    · apply normalizedFactors_prod one_ne_zero

-- DISSOLVED: normalizedFactors_mul

@[simp]
theorem normalizedFactors_pow {x : α} (n : ℕ) :
    normalizedFactors (x ^ n) = n • normalizedFactors x := by
  induction' n with n ih
  · simp
  by_cases h0 : x = 0
  · simp [h0, zero_pow n.succ_ne_zero, smul_zero]
  rw [pow_succ', succ_nsmul', normalizedFactors_mul h0 (pow_ne_zero _ h0), ih]

theorem _root_.Irreducible.normalizedFactors_pow {p : α} (hp : Irreducible p) (k : ℕ) :
    normalizedFactors (p ^ k) = Multiset.replicate k (normalize p) := by
  rw [UniqueFactorizationMonoid.normalizedFactors_pow, normalizedFactors_irreducible hp,
    Multiset.nsmul_singleton]

theorem normalizedFactors_prod_eq (s : Multiset α) (hs : ∀ a ∈ s, Irreducible a) :
    normalizedFactors s.prod = s.map normalize := by
  induction' s using Multiset.induction with a s ih
  · rw [Multiset.prod_zero, normalizedFactors_one, Multiset.map_zero]
  · have ia := hs a (Multiset.mem_cons_self a _)
    have ib := fun b h => hs b (Multiset.mem_cons_of_mem h)
    obtain rfl | ⟨b, hb⟩ := s.empty_or_exists_mem
    · rw [Multiset.cons_zero, Multiset.prod_singleton, Multiset.map_singleton,
        normalizedFactors_irreducible ia]
    haveI := nontrivial_of_ne b 0 (ib b hb).ne_zero
    rw [Multiset.prod_cons, Multiset.map_cons,
      normalizedFactors_mul ia.ne_zero (Multiset.prod_ne_zero fun h => (ib 0 h).ne_zero rfl),
      normalizedFactors_irreducible ia, ih ib, Multiset.singleton_add]

-- DISSOLVED: dvd_iff_normalizedFactors_le_normalizedFactors

theorem _root_.Associated.normalizedFactors_eq {a b : α} (h : Associated a b) :
    normalizedFactors a = normalizedFactors b := by
  unfold normalizedFactors
  have h' : ⇑(normalize (α := α)) = Associates.out ∘ Associates.mk := funext Associates.out_mk
  rw [h', ← Multiset.map_map, ← Multiset.map_map,
    Associates.rel_associated_iff_map_eq_map.mp (factors_rel_of_associated h)]

-- DISSOLVED: associated_iff_normalizedFactors_eq_normalizedFactors

theorem normalizedFactors_of_irreducible_pow {p : α} (hp : Irreducible p) (k : ℕ) :
    normalizedFactors (p ^ k) = Multiset.replicate k (normalize p) := by
  rw [normalizedFactors_pow, normalizedFactors_irreducible hp, Multiset.nsmul_singleton]

theorem zero_not_mem_normalizedFactors (x : α) : (0 : α) ∉ normalizedFactors x := fun h =>
  Prime.ne_zero (prime_of_normalized_factor _ h) rfl

theorem dvd_of_mem_normalizedFactors {a p : α} (H : p ∈ normalizedFactors a) : p ∣ a := by
  by_cases hcases : a = 0
  · rw [hcases]
    exact dvd_zero p
  · exact dvd_trans (Multiset.dvd_prod H) (Associated.dvd (normalizedFactors_prod hcases))

-- DISSOLVED: mem_normalizedFactors_iff

-- DISSOLVED: exists_associated_prime_pow_of_unique_normalized_factor

theorem normalizedFactors_prod_of_prime [Subsingleton αˣ] {m : Multiset α}
    (h : ∀ p ∈ m, Prime p) : normalizedFactors m.prod = m := by
  cases subsingleton_or_nontrivial α
  · obtain rfl : m = 0 := by
      refine Multiset.eq_zero_of_forall_not_mem fun x hx ↦ ?_
      simpa [Subsingleton.elim x 0] using h x hx
    simp
  · simpa only [← Multiset.rel_eq, ← associated_eq_eq] using
      prime_factors_unique prime_of_normalized_factor h
        (normalizedFactors_prod (m.prod_ne_zero_of_prime h))

theorem mem_normalizedFactors_eq_of_associated {a b c : α} (ha : a ∈ normalizedFactors c)
    (hb : b ∈ normalizedFactors c) (h : Associated a b) : a = b := by
  rw [← normalize_normalized_factor a ha, ← normalize_normalized_factor b hb,
    normalize_eq_normalize_iff]
  exact Associated.dvd_dvd h

-- DISSOLVED: normalizedFactors_pos

-- DISSOLVED: dvdNotUnit_iff_normalizedFactors_lt_normalizedFactors

theorem normalizedFactors_multiset_prod (s : Multiset α) (hs : 0 ∉ s) :
    normalizedFactors (s.prod) = (s.map normalizedFactors).sum := by
  cases subsingleton_or_nontrivial α
  · obtain rfl : s = 0 := by
      apply Multiset.eq_zero_of_forall_not_mem
      intro _
      convert hs
    simp
  induction s using Multiset.induction with
  | empty => simp
  | cons _ _ IH =>
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons, normalizedFactors_mul, IH]
    · exact fun h ↦ hs (Multiset.mem_cons_of_mem h)
    · exact fun h ↦ hs (h ▸ Multiset.mem_cons_self _ _)
    · apply Multiset.prod_ne_zero
      exact fun h ↦ hs (Multiset.mem_cons_of_mem h)

end UniqueFactorizationMonoid

namespace UniqueFactorizationMonoid

open scoped Classical

open Multiset Associates

variable [CancelCommMonoidWithZero α] [UniqueFactorizationMonoid α]

protected noncomputable def normalizationMonoid : NormalizationMonoid α :=
  normalizationMonoidOfMonoidHomRightInverse
    { toFun := fun a : Associates α =>
        if a = 0 then 0
        else
          ((normalizedFactors a).map
              (Classical.choose mk_surjective.hasRightInverse : Associates α → α)).prod
      map_one' := by nontriviality α; simp
      map_mul' := fun x y => by
        by_cases hx : x = 0
        · simp [hx]
        by_cases hy : y = 0
        · simp [hy]
        simp [hx, hy] }
    (by
      intro x
      dsimp
      by_cases hx : x = 0
      · simp [hx]
      have h : Associates.mkMonoidHom ∘ Classical.choose mk_surjective.hasRightInverse =
          (id : Associates α → Associates α) := by
        ext x
        rw [Function.comp_apply, mkMonoidHom_apply,
          Classical.choose_spec mk_surjective.hasRightInverse x]
        rfl
      rw [if_neg hx, ← mkMonoidHom_apply, MonoidHom.map_multiset_prod, map_map, h, map_id, ←
        associated_iff_eq]
      apply normalizedFactors_prod hx)

end UniqueFactorizationMonoid
