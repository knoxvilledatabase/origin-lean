/-
Extracted from RingTheory/UniqueFactorizationDomain/Basic.lean
Genuine: 20 of 34 | Dissolved: 12 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.SMulWithZero
import Mathlib.Data.ENat.Basic
import Mathlib.Data.Multiset.OrderedMonoid
import Mathlib.RingTheory.UniqueFactorizationDomain.Defs

/-!
# Basic results un unique factorization monoids

## Main results
* `prime_factors_unique`: the prime factors of an element in a cancellative
  commutative monoid with zero (e.g. an integral domain) are unique up to associates
* `UniqueFactorizationMonoid.factors_unique`: the irreducible factors of an element
  in a unique factorization monoid (e.g. a UFD) are unique up to associates
* `UniqueFactorizationMonoid.iff_exists_prime_factors`: unique factorization exists iff each nonzero
  elements factors into a product of primes
* `UniqueFactorizationMonoid.dvd_of_dvd_mul_left_of_no_prime_factors`: Euclid's lemma:
  if `a ∣ b * c` and `a` and `c` have no common prime factors, `a ∣ b`.
* `UniqueFactorizationMonoid.dvd_of_dvd_mul_right_of_no_prime_factors`: Euclid's lemma:
  if `a ∣ b * c` and `a` and `b` have no common prime factors, `a ∣ c`.
* `UniqueFactorizationMonoid.exists_reduced_factors`: in a UFM, we can divide out a common factor
  to get relatively prime elements.
-/

variable {α : Type*}

local infixl:50 " ~ᵤ " => Associated

namespace WfDvdMonoid

variable [CommMonoidWithZero α]

open Associates Nat

theorem of_wfDvdMonoid_associates (_ : WfDvdMonoid (Associates α)) : WfDvdMonoid α :=
  ⟨(mk_surjective.wellFounded_iff mk_dvdNotUnit_mk_iff.symm).2 wellFounded_dvdNotUnit⟩

variable [WfDvdMonoid α]

instance wfDvdMonoid_associates : WfDvdMonoid (Associates α) :=
  ⟨(mk_surjective.wellFounded_iff mk_dvdNotUnit_mk_iff.symm).1 wellFounded_dvdNotUnit⟩

theorem wellFoundedLT_associates : WellFoundedLT (Associates α) :=
  ⟨Subrelation.wf dvdNotUnit_of_lt wellFounded_dvdNotUnit⟩

theorem wellFounded_associates : WellFounded ((· < ·) : Associates α → Associates α → Prop) :=
  Subrelation.wf dvdNotUnit_of_lt wellFounded_dvdNotUnit

end WfDvdMonoid

theorem WfDvdMonoid.of_wellFoundedLT_associates [CancelCommMonoidWithZero α]
    (h : WellFoundedLT (Associates α)) : WfDvdMonoid α :=
  WfDvdMonoid.of_wfDvdMonoid_associates
    ⟨by
      convert h.wf
      ext
      exact Associates.dvdNotUnit_iff_lt⟩

theorem WfDvdMonoid.of_wellFounded_associates [CancelCommMonoidWithZero α]
    (h : WellFounded ((· < ·) : Associates α → Associates α → Prop)) : WfDvdMonoid α :=
  WfDvdMonoid.of_wfDvdMonoid_associates
    ⟨by
      convert h
      ext
      exact Associates.dvdNotUnit_iff_lt⟩

theorem WfDvdMonoid.iff_wellFounded_associates [CancelCommMonoidWithZero α] :
    WfDvdMonoid α ↔ WellFoundedLT (Associates α) :=
  ⟨by apply WfDvdMonoid.wellFoundedLT_associates, WfDvdMonoid.of_wellFoundedLT_associates⟩

instance Associates.ufm [CancelCommMonoidWithZero α] [UniqueFactorizationMonoid α] :
    UniqueFactorizationMonoid (Associates α) :=
  { (WfDvdMonoid.wfDvdMonoid_associates : WfDvdMonoid (Associates α)) with
    irreducible_iff_prime := by
      rw [← Associates.irreducible_iff_prime_iff]
      apply UniqueFactorizationMonoid.irreducible_iff_prime }

theorem prime_factors_unique [CancelCommMonoidWithZero α] :
    ∀ {f g : Multiset α},
      (∀ x ∈ f, Prime x) → (∀ x ∈ g, Prime x) → f.prod ~ᵤ g.prod → Multiset.Rel Associated f g := by
  classical
  intro f
  induction' f using Multiset.induction_on with p f ih
  · intros g _ hg h
    exact Multiset.rel_zero_left.2 <|
      Multiset.eq_zero_of_forall_not_mem fun x hx =>
        have : IsUnit g.prod := by simpa [associated_one_iff_isUnit] using h.symm
        (hg x hx).not_unit <|
          isUnit_iff_dvd_one.2 <| (Multiset.dvd_prod hx).trans (isUnit_iff_dvd_one.1 this)
  · intros g hf hg hfg
    let ⟨b, hbg, hb⟩ :=
      (exists_associated_mem_of_dvd_prod (hf p (by simp)) fun q hq => hg _ hq) <|
        hfg.dvd_iff_dvd_right.1 (show p ∣ (p ::ₘ f).prod by simp)
    haveI := Classical.decEq α
    rw [← Multiset.cons_erase hbg]
    exact
      Multiset.Rel.cons hb
        (ih (fun q hq => hf _ (by simp [hq]))
          (fun {q} (hq : q ∈ g.erase b) => hg q (Multiset.mem_of_mem_erase hq))
          (Associated.of_mul_left
            (by rwa [← Multiset.prod_cons, ← Multiset.prod_cons, Multiset.cons_erase hbg]) hb
            (hf p (by simp)).ne_zero))

namespace UniqueFactorizationMonoid

variable [CancelCommMonoidWithZero α] [UniqueFactorizationMonoid α]

theorem factors_unique {f g : Multiset α} (hf : ∀ x ∈ f, Irreducible x)
    (hg : ∀ x ∈ g, Irreducible x) (h : f.prod ~ᵤ g.prod) : Multiset.Rel Associated f g :=
  prime_factors_unique (fun x hx => UniqueFactorizationMonoid.irreducible_iff_prime.mp (hf x hx))
    (fun x hx => UniqueFactorizationMonoid.irreducible_iff_prime.mp (hg x hx)) h

end UniqueFactorizationMonoid

theorem prime_factors_irreducible [CancelCommMonoidWithZero α] {a : α} {f : Multiset α}
    (ha : Irreducible a) (pfa : (∀ b ∈ f, Prime b) ∧ f.prod ~ᵤ a) : ∃ p, a ~ᵤ p ∧ f = {p} := by
  haveI := Classical.decEq α
  refine @Multiset.induction_on _
    (fun g => (g.prod ~ᵤ a) → (∀ b ∈ g, Prime b) → ∃ p, a ~ᵤ p ∧ g = {p}) f ?_ ?_ pfa.2 pfa.1
  · intro h; exact (ha.not_unit (associated_one_iff_isUnit.1 (Associated.symm h))).elim
  · rintro p s _ ⟨u, hu⟩ hs
    use p
    have hs0 : s = 0 := by
      by_contra hs0
      obtain ⟨q, hq⟩ := Multiset.exists_mem_of_ne_zero hs0
      apply (hs q (by simp [hq])).2.1
      refine (ha.isUnit_or_isUnit (?_ : _ = p * ↑u * (s.erase q).prod * _)).resolve_left ?_
      · rw [mul_right_comm _ _ q, mul_assoc, ← Multiset.prod_cons, Multiset.cons_erase hq, ← hu,
          mul_comm, mul_comm p _, mul_assoc]
        simp
      apply mt isUnit_of_mul_isUnit_left (mt isUnit_of_mul_isUnit_left _)
      apply (hs p (Multiset.mem_cons_self _ _)).2.1
    simp only [mul_one, Multiset.prod_cons, Multiset.prod_zero, hs0] at *
    exact ⟨Associated.symm ⟨u, hu⟩, rfl⟩

-- DISSOLVED: irreducible_iff_prime_of_exists_unique_irreducible_factors

namespace UniqueFactorizationMonoid

variable [CancelCommMonoidWithZero α]

variable [UniqueFactorizationMonoid α]

@[simp]
theorem factors_one : factors (1 : α) = 0 := by
  nontriviality α using factors
  rw [← Multiset.rel_zero_right]
  refine factors_unique irreducible_of_factor (fun x hx => (Multiset.not_mem_zero x hx).elim) ?_
  rw [Multiset.prod_zero]
  exact factors_prod one_ne_zero

-- DISSOLVED: exists_mem_factors_of_dvd

-- DISSOLVED: exists_mem_factors

open Classical in

-- DISSOLVED: factors_mul

theorem factors_pow {x : α} (n : ℕ) :
    Multiset.Rel Associated (factors (x ^ n)) (n • factors x) := by
  match n with
  | 0 => rw [zero_smul, pow_zero, factors_one, Multiset.rel_zero_right]
  | n+1 =>
    by_cases h0 : x = 0
    · simp [h0, zero_pow n.succ_ne_zero, smul_zero]
    · rw [pow_succ', succ_nsmul']
      refine Multiset.Rel.trans _ (factors_mul h0 (pow_ne_zero n h0)) ?_
      refine Multiset.Rel.add ?_ <| factors_pow n
      exact Multiset.rel_refl_of_refl_on fun y _ => Associated.refl _

-- DISSOLVED: factors_pos

open Multiset in

-- DISSOLVED: factors_pow_count_prod

theorem factors_rel_of_associated {a b : α} (h : Associated a b) :
    Multiset.Rel Associated (factors a) (factors b) := by
  rcases iff_iff_and_or_not_and_not.mp h.eq_zero_iff with (⟨rfl, rfl⟩ | ⟨ha, hb⟩)
  · simp
  · refine factors_unique irreducible_of_factor irreducible_of_factor ?_
    exact ((factors_prod ha).trans h).trans (factors_prod hb).symm

end UniqueFactorizationMonoid

namespace Associates

attribute [local instance] Associated.setoid

open Multiset UniqueFactorizationMonoid

variable [CancelCommMonoidWithZero α] [UniqueFactorizationMonoid α]

theorem unique' {p q : Multiset (Associates α)} :
    (∀ a ∈ p, Irreducible a) → (∀ a ∈ q, Irreducible a) → p.prod = q.prod → p = q := by
  apply Multiset.induction_on_multiset_quot p
  apply Multiset.induction_on_multiset_quot q
  intro s t hs ht eq
  refine Multiset.map_mk_eq_map_mk_of_rel (UniqueFactorizationMonoid.factors_unique ?_ ?_ ?_)
  · exact fun a ha => irreducible_mk.1 <| hs _ <| Multiset.mem_map_of_mem _ ha
  · exact fun a ha => irreducible_mk.1 <| ht _ <| Multiset.mem_map_of_mem _ ha
  have eq' : (Quot.mk Setoid.r : α → Associates α) = Associates.mk := funext quot_mk_eq_mk
  rwa [eq', prod_mk, prod_mk, mk_eq_mk_iff_associated] at eq

theorem prod_le_prod_iff_le [Nontrivial α] {p q : Multiset (Associates α)}
    (hp : ∀ a ∈ p, Irreducible a) (hq : ∀ a ∈ q, Irreducible a) : p.prod ≤ q.prod ↔ p ≤ q := by
  refine ⟨?_, prod_le_prod⟩
  rintro ⟨c, eqc⟩
  refine Multiset.le_iff_exists_add.2 ⟨factors c, unique' hq (fun x hx ↦ ?_) ?_⟩
  · obtain h | h := Multiset.mem_add.1 hx
    · exact hp x h
    · exact irreducible_of_factor _ h
  · rw [eqc, Multiset.prod_add]
    congr
    refine associated_iff_eq.mp (factors_prod fun hc => ?_).symm
    refine not_irreducible_zero (hq _ ?_)
    rw [← prod_eq_zero_iff, eqc, hc, mul_zero]

end Associates

section ExistsPrimeFactors

variable [CancelCommMonoidWithZero α]

variable (pf : ∀ a : α, a ≠ 0 → ∃ f : Multiset α, (∀ b ∈ f, Prime b) ∧ f.prod ~ᵤ a)

include pf

theorem WfDvdMonoid.of_exists_prime_factors : WfDvdMonoid α :=
  ⟨by
    classical
      refine RelHomClass.wellFounded
        (RelHom.mk ?_ ?_ : (DvdNotUnit : α → α → Prop) →r ((· < ·) : ℕ∞ → ℕ∞ → Prop)) wellFounded_lt
      · intro a
        by_cases h : a = 0
        · exact ⊤
        exact ↑(Multiset.card (Classical.choose (pf a h)))
      rintro a b ⟨ane0, ⟨c, hc, b_eq⟩⟩
      rw [dif_neg ane0]
      by_cases h : b = 0
      · simp [h, lt_top_iff_ne_top]
      · rw [dif_neg h, Nat.cast_lt]
        have cne0 : c ≠ 0 := by
          refine mt (fun con => ?_) h
          rw [b_eq, con, mul_zero]
        calc
          Multiset.card (Classical.choose (pf a ane0)) <
              _ + Multiset.card (Classical.choose (pf c cne0)) :=
            lt_add_of_pos_right _
              (Multiset.card_pos.mpr fun con => hc (associated_one_iff_isUnit.mp ?_))
          _ = Multiset.card (Classical.choose (pf a ane0) + Classical.choose (pf c cne0)) :=
            (Multiset.card_add _ _).symm
          _ = Multiset.card (Classical.choose (pf b h)) :=
            Multiset.card_eq_card_of_rel
            (prime_factors_unique ?_ (Classical.choose_spec (pf _ h)).1 ?_)

        · convert (Classical.choose_spec (pf c cne0)).2.symm
          rw [con, Multiset.prod_zero]
        · intro x hadd
          rw [Multiset.mem_add] at hadd
          cases' hadd with h h <;> apply (Classical.choose_spec (pf _ _)).1 _ h <;> assumption
        · rw [Multiset.prod_add]
          trans a * c
          · apply Associated.mul_mul <;> apply (Classical.choose_spec (pf _ _)).2 <;> assumption
          · rw [← b_eq]
            apply (Classical.choose_spec (pf _ _)).2.symm; assumption⟩

theorem irreducible_iff_prime_of_exists_prime_factors {p : α} : Irreducible p ↔ Prime p := by
  by_cases hp0 : p = 0
  · simp [hp0]
  refine ⟨fun h => ?_, Prime.irreducible⟩
  obtain ⟨f, hf⟩ := pf p hp0
  obtain ⟨q, hq, rfl⟩ := prime_factors_irreducible h hf
  rw [hq.prime_iff]
  exact hf.1 q (Multiset.mem_singleton_self _)

theorem UniqueFactorizationMonoid.of_exists_prime_factors : UniqueFactorizationMonoid α :=
  { WfDvdMonoid.of_exists_prime_factors pf with
    irreducible_iff_prime := irreducible_iff_prime_of_exists_prime_factors pf }

end ExistsPrimeFactors

-- DISSOLVED: UniqueFactorizationMonoid.iff_exists_prime_factors

section

variable {β : Type*} [CancelCommMonoidWithZero α] [CancelCommMonoidWithZero β]

theorem MulEquiv.uniqueFactorizationMonoid (e : α ≃* β) (hα : UniqueFactorizationMonoid α) :
    UniqueFactorizationMonoid β := by
  rw [UniqueFactorizationMonoid.iff_exists_prime_factors] at hα ⊢
  intro a ha
  obtain ⟨w, hp, u, h⟩ :=
    hα (e.symm a) fun h =>
      ha <| by
        convert← map_zero e
        simp [← h]
  exact
    ⟨w.map e, fun b hb =>
        let ⟨c, hc, he⟩ := Multiset.mem_map.1 hb
        he ▸ e.prime_iff.1 (hp c hc),
        Units.map e.toMonoidHom u,
      by
        rw [Multiset.prod_hom, toMonoidHom_eq_coe, Units.coe_map, MonoidHom.coe_coe, ← map_mul e, h,
          apply_symm_apply]⟩

theorem MulEquiv.uniqueFactorizationMonoid_iff (e : α ≃* β) :
    UniqueFactorizationMonoid α ↔ UniqueFactorizationMonoid β :=
  ⟨e.uniqueFactorizationMonoid, e.symm.uniqueFactorizationMonoid⟩

end

namespace UniqueFactorizationMonoid

-- DISSOLVED: of_exists_unique_irreducible_factors

variable {R : Type*} [CancelCommMonoidWithZero R] [UniqueFactorizationMonoid R]

-- DISSOLVED: isRelPrime_iff_no_prime_factors

-- DISSOLVED: dvd_of_dvd_mul_left_of_no_prime_factors

-- DISSOLVED: dvd_of_dvd_mul_right_of_no_prime_factors

theorem exists_reduced_factors :
    ∀ a ≠ (0 : R), ∀ b,
      ∃ a' b' c', IsRelPrime a' b' ∧ c' * a' = a ∧ c' * b' = b := by
  intro a
  refine induction_on_prime a ?_ ?_ ?_
  · intros
    contradiction
  · intro a a_unit _ b
    use a, b, 1
    constructor
    · intro p p_dvd_a _
      exact isUnit_of_dvd_unit p_dvd_a a_unit
    · simp
  · intro a p a_ne_zero p_prime ih_a pa_ne_zero b
    by_cases h : p ∣ b
    · rcases h with ⟨b, rfl⟩
      obtain ⟨a', b', c', no_factor, ha', hb'⟩ := ih_a a_ne_zero b
      refine ⟨a', b', p * c', @no_factor, ?_, ?_⟩
      · rw [mul_assoc, ha']
      · rw [mul_assoc, hb']
    · obtain ⟨a', b', c', coprime, rfl, rfl⟩ := ih_a a_ne_zero b
      refine ⟨p * a', b', c', ?_, mul_left_comm _ _ _, rfl⟩
      intro q q_dvd_pa' q_dvd_b'
      cases' p_prime.left_dvd_or_dvd_right_of_dvd_mul q_dvd_pa' with p_dvd_q q_dvd_a'
      · have : p ∣ c' * b' := dvd_mul_of_dvd_right (p_dvd_q.trans q_dvd_b') _
        contradiction
      exact coprime q_dvd_a' q_dvd_b'

-- DISSOLVED: exists_reduced_factors'

end UniqueFactorizationMonoid
