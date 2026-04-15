/-
Extracted from RingTheory/UniqueFactorizationDomain/FactorSet.lean
Genuine: 46 of 78 | Dissolved: 25 | Infrastructure: 7
-/
import Origin.Core
import Mathlib.Data.Finsupp.Multiset
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.Tactic.Ring

/-!
# Set of factors

## Main definitions
* `Associates.FactorSet`: multiset of factors of an element, unique up to propositional equality.
* `Associates.factors`: determine the `FactorSet` for a given element.

## TODO
* set up the complete lattice structure on `FactorSet`.

-/

variable {α : Type*}

local infixl:50 " ~ᵤ " => Associated

namespace Associates

open UniqueFactorizationMonoid Associated Multiset

variable [CancelCommMonoidWithZero α]

abbrev FactorSet.{u} (α : Type u) [CancelCommMonoidWithZero α] : Type u :=
  WithTop (Multiset { a : Associates α // Irreducible a })

attribute [local instance] Associated.setoid

theorem FactorSet.coe_add {a b : Multiset { a : Associates α // Irreducible a }} :
    (↑(a + b) : FactorSet α) = a + b := by norm_cast

theorem FactorSet.sup_add_inf_eq_add [DecidableEq (Associates α)] :
    ∀ a b : FactorSet α, a ⊔ b + a ⊓ b = a + b
  | ⊤, b => show ⊤ ⊔ b + ⊤ ⊓ b = ⊤ + b by simp
  | a, ⊤ => show a ⊔ ⊤ + a ⊓ ⊤ = a + ⊤ by simp
  | WithTop.some a, WithTop.some b =>
    show (a : FactorSet α) ⊔ b + (a : FactorSet α) ⊓ b = a + b by
      rw [← WithTop.coe_sup, ← WithTop.coe_inf, ← WithTop.coe_add, ← WithTop.coe_add,
        WithTop.coe_eq_coe]
      exact Multiset.union_add_inter _ _

def FactorSet.prod : FactorSet α → Associates α
  | ⊤ => 0
  | WithTop.some s => (s.map (↑)).prod

@[simp]
theorem prod_top : (⊤ : FactorSet α).prod = 0 :=
  rfl

@[simp]
theorem prod_coe {s : Multiset { a : Associates α // Irreducible a }} :
    FactorSet.prod (s : FactorSet α) = (s.map (↑)).prod :=
  rfl

@[simp]
theorem prod_add : ∀ a b : FactorSet α, (a + b).prod = a.prod * b.prod
  | ⊤, b => show (⊤ + b).prod = (⊤ : FactorSet α).prod * b.prod by simp
  | a, ⊤ => show (a + ⊤).prod = a.prod * (⊤ : FactorSet α).prod by simp
  | WithTop.some a, WithTop.some b => by
    rw [← FactorSet.coe_add, prod_coe, prod_coe, prod_coe, Multiset.map_add, Multiset.prod_add]

@[gcongr]
theorem prod_mono : ∀ {a b : FactorSet α}, a ≤ b → a.prod ≤ b.prod
  | ⊤, b, h => by
    have : b = ⊤ := top_unique h
    rw [this, prod_top]
  | a, ⊤, _ => show a.prod ≤ (⊤ : FactorSet α).prod by simp
  | WithTop.some _, WithTop.some _, h =>
    prod_le_prod <| Multiset.map_le_map <| WithTop.coe_le_coe.1 <| h

theorem FactorSet.prod_eq_zero_iff [Nontrivial α] (p : FactorSet α) : p.prod = 0 ↔ p = ⊤ := by
  unfold FactorSet at p
  induction p  -- TODO: `induction_eliminator` doesn't work with `abbrev`
  · simp only [eq_self_iff_true, Associates.prod_top]
  · rw [prod_coe, Multiset.prod_eq_zero_iff, Multiset.mem_map, eq_false WithTop.coe_ne_top,
      iff_false, not_exists]
    exact fun a => not_and_of_not_right _ a.prop.ne_zero

section count

variable [DecidableEq (Associates α)]

def bcount (p : { a : Associates α // Irreducible a }) :
    FactorSet α → ℕ
  | ⊤ => 0
  | WithTop.some s => s.count p

variable [∀ p : Associates α, Decidable (Irreducible p)] {p : Associates α}

def count (p : Associates α) : FactorSet α → ℕ :=
  if hp : Irreducible p then bcount ⟨p, hp⟩ else 0

@[simp]
theorem count_some (hp : Irreducible p) (s : Multiset _) :
    count p (WithTop.some s) = s.count ⟨p, hp⟩ := by
  simp only [count, dif_pos hp, bcount]

@[simp]
theorem count_zero (hp : Irreducible p) : count p (0 : FactorSet α) = 0 := by
  simp only [count, dif_pos hp, bcount, Multiset.count_zero]

theorem count_reducible (hp : ¬Irreducible p) : count p = 0 := dif_neg hp

end count

section Mem

def BfactorSetMem : { a : Associates α // Irreducible a } → FactorSet α → Prop
  | _, ⊤ => True
  | p, some l => p ∈ l

def FactorSetMem (s : FactorSet α) (p : Associates α) : Prop :=
  letI : Decidable (Irreducible p) := Classical.dec _
  if hp : Irreducible p then BfactorSetMem ⟨p, hp⟩ s else False

instance : Membership (Associates α) (FactorSet α) :=
  ⟨FactorSetMem⟩

@[simp]
theorem factorSetMem_eq_mem (p : Associates α) (s : FactorSet α) : FactorSetMem s p = (p ∈ s) :=
  rfl

theorem mem_factorSet_top {p : Associates α} {hp : Irreducible p} : p ∈ (⊤ : FactorSet α) := by
  dsimp only [Membership.mem]; dsimp only [FactorSetMem]; split_ifs; exact trivial

theorem mem_factorSet_some {p : Associates α} {hp : Irreducible p}
    {l : Multiset { a : Associates α // Irreducible a }} :
    p ∈ (l : FactorSet α) ↔ Subtype.mk p hp ∈ l := by
  dsimp only [Membership.mem]; dsimp only [FactorSetMem]; split_ifs; rfl

theorem reducible_not_mem_factorSet {p : Associates α} (hp : ¬Irreducible p) (s : FactorSet α) :
    ¬p ∈ s := fun h ↦ by
  rwa [← factorSetMem_eq_mem, FactorSetMem, dif_neg hp] at h

theorem irreducible_of_mem_factorSet {p : Associates α} {s : FactorSet α} (h : p ∈ s) :
    Irreducible p :=
  by_contra fun hp ↦ reducible_not_mem_factorSet hp s h

end Mem

variable [UniqueFactorizationMonoid α]

theorem FactorSet.unique [Nontrivial α] {p q : FactorSet α} (h : p.prod = q.prod) : p = q := by
  -- TODO: `induction_eliminator` doesn't work with `abbrev`
  unfold FactorSet at p q
  induction p <;> induction q
  · rfl
  · rw [eq_comm, ← FactorSet.prod_eq_zero_iff, ← h, Associates.prod_top]
  · rw [← FactorSet.prod_eq_zero_iff, h, Associates.prod_top]
  · congr 1
    rw [← Multiset.map_eq_map Subtype.coe_injective]
    apply unique' _ _ h <;>
      · intro a ha
        obtain ⟨⟨a', irred⟩, -, rfl⟩ := Multiset.mem_map.mp ha
        rwa [Subtype.coe_mk]

noncomputable def factors' (a : α) : Multiset { a : Associates α // Irreducible a } :=
  (factors a).pmap (fun a ha => ⟨Associates.mk a, irreducible_mk.2 ha⟩) irreducible_of_factor

@[simp]
theorem map_subtype_coe_factors' {a : α} :
    (factors' a).map (↑) = (factors a).map Associates.mk := by
  simp [factors', Multiset.map_pmap, Multiset.pmap_eq_map]

theorem factors'_cong {a b : α} (h : a ~ᵤ b) : factors' a = factors' b := by
  obtain rfl | hb := eq_or_ne b 0
  · rw [associated_zero_iff_eq_zero] at h
    rw [h]
  have ha : a ≠ 0 := by
    contrapose! hb with ha
    rw [← associated_zero_iff_eq_zero, ← ha]
    exact h.symm
  rw [← Multiset.map_eq_map Subtype.coe_injective, map_subtype_coe_factors',
    map_subtype_coe_factors', ← rel_associated_iff_map_eq_map]
  exact
    factors_unique irreducible_of_factor irreducible_of_factor
      ((factors_prod ha).trans <| h.trans <| (factors_prod hb).symm)

noncomputable def factors (a : Associates α) : FactorSet α := by
  classical refine if h : a = 0 then ⊤ else Quotient.hrecOn a (fun x _ => factors' x) ?_ h
  intro a b hab
  apply Function.hfunext
  · have : a ~ᵤ 0 ↔ b ~ᵤ 0 := Iff.intro (fun ha0 => hab.symm.trans ha0) fun hb0 => hab.trans hb0
    simp only [associated_zero_iff_eq_zero] at this
    simp only [quotient_mk_eq_mk, this, mk_eq_zero]
  exact fun ha hb _ => heq_of_eq <| congr_arg some <| factors'_cong hab

@[simp]
theorem factors_zero : (0 : Associates α).factors = ⊤ :=
  dif_pos rfl

-- DISSOLVED: factors_mk

@[simp]
theorem factors_prod (a : Associates α) : a.factors.prod = a := by
  rcases Associates.mk_surjective a with ⟨a, rfl⟩
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · simp [ha, prod_mk, mk_eq_mk_iff_associated, UniqueFactorizationMonoid.factors_prod,
      -Quotient.eq]

@[simp]
theorem prod_factors [Nontrivial α] (s : FactorSet α) : s.prod.factors = s :=
  FactorSet.unique <| factors_prod _

@[nontriviality]
theorem factors_subsingleton [Subsingleton α] {a : Associates α} : a.factors = ⊤ := by
  have : Subsingleton (Associates α) := inferInstance
  convert factors_zero

theorem factors_eq_top_iff_zero {a : Associates α} : a.factors = ⊤ ↔ a = 0 := by
  nontriviality α
  exact ⟨fun h ↦ by rwa [← factors_prod a, FactorSet.prod_eq_zero_iff], fun h ↦ h ▸ factors_zero⟩

-- DISSOLVED: factors_eq_some_iff_ne_zero

theorem eq_of_factors_eq_factors {a b : Associates α} (h : a.factors = b.factors) : a = b := by
  have : a.factors.prod = b.factors.prod := by rw [h]
  rwa [factors_prod, factors_prod] at this

theorem eq_of_prod_eq_prod [Nontrivial α] {a b : FactorSet α} (h : a.prod = b.prod) : a = b := by
  have : a.prod.factors = b.prod.factors := by rw [h]
  rwa [prod_factors, prod_factors] at this

@[simp]
theorem factors_mul (a b : Associates α) : (a * b).factors = a.factors + b.factors := by
  nontriviality α
  refine eq_of_prod_eq_prod <| eq_of_factors_eq_factors ?_
  rw [prod_add, factors_prod, factors_prod, factors_prod]

@[gcongr]
theorem factors_mono : ∀ {a b : Associates α}, a ≤ b → a.factors ≤ b.factors
  | s, t, ⟨d, eq⟩ => by rw [eq, factors_mul]; exact le_add_of_nonneg_right bot_le

@[simp]
theorem factors_le {a b : Associates α} : a.factors ≤ b.factors ↔ a ≤ b := by
  refine ⟨fun h ↦ ?_, factors_mono⟩
  have : a.factors.prod ≤ b.factors.prod := prod_mono h
  rwa [factors_prod, factors_prod] at this

section count

variable [DecidableEq (Associates α)] [∀ p : Associates α, Decidable (Irreducible p)]

-- DISSOLVED: eq_factors_of_eq_counts

-- DISSOLVED: eq_of_eq_counts

-- DISSOLVED: count_le_count_of_factors_le

-- DISSOLVED: count_le_count_of_le

end count

theorem prod_le [Nontrivial α] {a b : FactorSet α} : a.prod ≤ b.prod ↔ a ≤ b := by
  refine ⟨fun h ↦ ?_, prod_mono⟩
  have : a.prod.factors ≤ b.prod.factors := factors_mono h
  rwa [prod_factors, prod_factors] at this

open Classical in

noncomputable instance : Max (Associates α) :=
  ⟨fun a b => (a.factors ⊔ b.factors).prod⟩

open Classical in

noncomputable instance : Min (Associates α) :=
  ⟨fun a b => (a.factors ⊓ b.factors).prod⟩

open Classical in

noncomputable instance : Lattice (Associates α) :=
  { Associates.instPartialOrder with
    sup := (· ⊔ ·)
    inf := (· ⊓ ·)
    sup_le := fun _ _ c hac hbc =>
      factors_prod c ▸ prod_mono (sup_le (factors_mono hac) (factors_mono hbc))
    le_sup_left := fun a _ => le_trans (le_of_eq (factors_prod a).symm) <| prod_mono <| le_sup_left
    le_sup_right := fun _ b =>
      le_trans (le_of_eq (factors_prod b).symm) <| prod_mono <| le_sup_right
    le_inf := fun a _ _ hac hbc =>
      factors_prod a ▸ prod_mono (le_inf (factors_mono hac) (factors_mono hbc))
    inf_le_left := fun a _ => le_trans (prod_mono inf_le_left) (le_of_eq (factors_prod a))
    inf_le_right := fun _ b => le_trans (prod_mono inf_le_right) (le_of_eq (factors_prod b)) }

open Classical in

theorem sup_mul_inf (a b : Associates α) : (a ⊔ b) * (a ⊓ b) = a * b :=
  show (a.factors ⊔ b.factors).prod * (a.factors ⊓ b.factors).prod = a * b by
    nontriviality α
    refine eq_of_factors_eq_factors ?_
    rw [← prod_add, prod_factors, factors_mul, FactorSet.sup_add_inf_eq_add]

theorem dvd_of_mem_factors {a p : Associates α} (hm : p ∈ factors a) :
    p ∣ a := by
  rcases eq_or_ne a 0 with rfl | ha0
  · exact dvd_zero p
  obtain ⟨a0, nza, ha'⟩ := exists_non_zero_rep ha0
  rw [← Associates.factors_prod a]
  rw [← ha', factors_mk a0 nza] at hm ⊢
  rw [prod_coe]
  apply Multiset.dvd_prod; apply Multiset.mem_map.mpr
  exact ⟨⟨p, irreducible_of_mem_factorSet hm⟩, mem_factorSet_some.mp hm, rfl⟩

-- DISSOLVED: dvd_of_mem_factors'

-- DISSOLVED: mem_factors'_of_dvd

-- DISSOLVED: mem_factors'_iff_dvd

-- DISSOLVED: mem_factors_of_dvd

-- DISSOLVED: mem_factors_iff_dvd

open Classical in

-- DISSOLVED: exists_prime_dvd_of_not_inf_one

-- DISSOLVED: coprime_iff_inf_one

theorem factors_self [Nontrivial α] {p : Associates α} (hp : Irreducible p) :
    p.factors = WithTop.some {⟨p, hp⟩} :=
  eq_of_prod_eq_prod
    (by rw [factors_prod, FactorSet.prod.eq_def]; dsimp; rw [prod_singleton])

theorem factors_prime_pow [Nontrivial α] {p : Associates α} (hp : Irreducible p) (k : ℕ) :
    factors (p ^ k) = WithTop.some (Multiset.replicate k ⟨p, hp⟩) :=
  eq_of_prod_eq_prod
    (by
      rw [Associates.factors_prod, FactorSet.prod.eq_def]
      dsimp; rw [Multiset.map_replicate, Multiset.prod_replicate, Subtype.coe_mk])

-- DISSOLVED: prime_pow_le_iff_le_bcount

@[simp]
theorem factors_one [Nontrivial α] : factors (1 : Associates α) = 0 := by
  apply eq_of_prod_eq_prod
  rw [Associates.factors_prod]
  exact Multiset.prod_zero

@[simp]
theorem pow_factors [Nontrivial α] {a : Associates α} {k : ℕ} :
    (a ^ k).factors = k • a.factors := by
  induction' k with n h
  · rw [zero_nsmul, pow_zero]
    exact factors_one
  · rw [pow_succ, succ_nsmul, factors_mul, h]

section count

variable [DecidableEq (Associates α)] [∀ p : Associates α, Decidable (Irreducible p)]

-- DISSOLVED: prime_pow_dvd_iff_le

-- DISSOLVED: le_of_count_ne_zero

-- DISSOLVED: count_ne_zero_iff_dvd

theorem count_self [Nontrivial α] {p : Associates α}
    (hp : Irreducible p) : p.count p.factors = 1 := by
  simp [factors_self hp, Associates.count_some hp]

theorem count_eq_zero_of_ne {p q : Associates α} (hp : Irreducible p)
    (hq : Irreducible q) (h : p ≠ q) : p.count q.factors = 0 :=
  not_ne_iff.mp fun h' ↦ h <| associated_iff_eq.mp <| hp.associated_of_dvd hq <|
    le_of_count_ne_zero hq.ne_zero hp h'

-- DISSOLVED: count_mul

-- DISSOLVED: count_of_coprime

-- DISSOLVED: count_mul_of_coprime

theorem count_mul_of_coprime' {a b : Associates α} {p : Associates α}
    (hp : Irreducible p) (hab : ∀ d, d ∣ a → d ∣ b → ¬Prime d) :
    count p (a * b).factors = count p a.factors ∨ count p (a * b).factors = count p b.factors := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  rw [count_mul ha hb hp]
  cases' count_of_coprime ha hb hab hp with ha0 hb0
  · apply Or.intro_right
    rw [ha0, zero_add]
  · apply Or.intro_left
    rw [hb0, add_zero]

-- DISSOLVED: dvd_count_of_dvd_count_mul

-- DISSOLVED: count_pow

-- DISSOLVED: dvd_count_pow

-- DISSOLVED: is_pow_of_dvd_count

theorem eq_pow_count_factors_of_dvd_pow {p a : Associates α}
    (hp : Irreducible p) {n : ℕ} (h : a ∣ p ^ n) : a = p ^ p.count a.factors := by
  nontriviality α
  have hph := pow_ne_zero n hp.ne_zero
  have ha := ne_zero_of_dvd_ne_zero hph h
  apply eq_of_eq_counts ha (pow_ne_zero _ hp.ne_zero)
  have eq_zero_of_ne : ∀ q : Associates α, Irreducible q → q ≠ p → _ = 0 := fun q hq h' =>
    Nat.eq_zero_of_le_zero <| by
      convert count_le_count_of_le hph hq h
      symm
      rw [count_pow hp.ne_zero hq, count_eq_zero_of_ne hq hp h', mul_zero]
  intro q hq
  rw [count_pow hp.ne_zero hq]
  by_cases h : q = p
  · rw [h, count_self hp, mul_one]
  · rw [count_eq_zero_of_ne hq hp h, mul_zero, eq_zero_of_ne q hq h]

theorem count_factors_eq_find_of_dvd_pow {a p : Associates α}
    (hp : Irreducible p) [∀ n : ℕ, Decidable (a ∣ p ^ n)] {n : ℕ} (h : a ∣ p ^ n) :
    @Nat.find (fun n => a ∣ p ^ n) _ ⟨n, h⟩ = p.count a.factors := by
  apply le_antisymm
  · refine Nat.find_le ⟨1, ?_⟩
    rw [mul_one]
    symm
    exact eq_pow_count_factors_of_dvd_pow hp h
  · have hph := pow_ne_zero (@Nat.find (fun n => a ∣ p ^ n) _ ⟨n, h⟩) hp.ne_zero
    cases' subsingleton_or_nontrivial α with hα hα
    · simp [eq_iff_true_of_subsingleton] at hph
    convert count_le_count_of_le hph hp (@Nat.find_spec (fun n => a ∣ p ^ n) _ ⟨n, h⟩)
    rw [count_pow hp.ne_zero hp, count_self hp, mul_one]

end count

-- DISSOLVED: eq_pow_of_mul_eq_pow

theorem eq_pow_find_of_dvd_irreducible_pow {a p : Associates α} (hp : Irreducible p)
    [∀ n : ℕ, Decidable (a ∣ p ^ n)] {n : ℕ} (h : a ∣ p ^ n) :
    a = p ^ @Nat.find (fun n => a ∣ p ^ n) _ ⟨n, h⟩ := by
  classical rw [count_factors_eq_find_of_dvd_pow hp, ← eq_pow_count_factors_of_dvd_pow hp h]
  exact h

end Associates
