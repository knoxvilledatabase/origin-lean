/-
Extracted from RingTheory/UniqueFactorizationDomain/Basic.lean
Genuine: 7 of 11 | Dissolved: 1 | Infrastructure: 3
-/
import Origin.Core

/-!
# Basic results on unique factorization monoids

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

assert_not_exists Field

variable {α : Type*}

local infixl:50 " ~ᵤ " => Associated

namespace WfDvdMonoid

variable [CommMonoidWithZero α]

open Associates Nat

theorem of_wfDvdMonoid_associates (_ : WfDvdMonoid (Associates α)) : WfDvdMonoid α :=
  ⟨(mk_surjective.wellFounded_iff mk_dvdNotUnit_mk_iff.symm).2 wellFounded_dvdNotUnit⟩

variable [WfDvdMonoid α]

-- INSTANCE (free from Core): wfDvdMonoid_associates

theorem wellFoundedLT_associates : WellFoundedLT (Associates α) :=
  ⟨Subrelation.wf dvdNotUnit_of_lt wellFounded_dvdNotUnit⟩

end WfDvdMonoid

theorem WfDvdMonoid.of_wellFoundedLT_associates [CommMonoidWithZero α] [IsCancelMulZero α]
    (h : WellFoundedLT (Associates α)) : WfDvdMonoid α :=
  WfDvdMonoid.of_wfDvdMonoid_associates
    ⟨by
      convert h.wf
      ext
      exact Associates.dvdNotUnit_iff_lt⟩

theorem WfDvdMonoid.iff_wellFounded_associates [CommMonoidWithZero α] [IsCancelMulZero α] :
    WfDvdMonoid α ↔ WellFoundedLT (Associates α) :=
  ⟨by apply WfDvdMonoid.wellFoundedLT_associates, WfDvdMonoid.of_wellFoundedLT_associates⟩

-- INSTANCE (free from Core): Associates.ufm

theorem prime_factors_unique [CommMonoidWithZero α] [IsCancelMulZero α] :
    ∀ {f g : Multiset α},
      (∀ x ∈ f, Prime x) → (∀ x ∈ g, Prime x) → f.prod ~ᵤ g.prod → Multiset.Rel Associated f g := by
  classical
  intro f
  induction f using Multiset.induction_on with
  | empty =>
    intro g _ hg h
    exact Multiset.rel_zero_left.2 <|
      Multiset.eq_zero_of_forall_notMem fun x hx =>
        have : IsUnit g.prod := by simpa [associated_one_iff_isUnit] using h.symm
        (hg x hx).not_unit <|
          isUnit_iff_dvd_one.2 <| (Multiset.dvd_prod hx).trans (isUnit_iff_dvd_one.1 this)
  | cons p f ih =>
    intro g hf hg hfg
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

variable [CommMonoidWithZero α] [UniqueFactorizationMonoid α]

theorem factors_unique {f g : Multiset α} (hf : ∀ x ∈ f, Irreducible x)
    (hg : ∀ x ∈ g, Irreducible x) (h : f.prod ~ᵤ g.prod) : Multiset.Rel Associated f g :=
  prime_factors_unique (fun x hx => UniqueFactorizationMonoid.irreducible_iff_prime.mp (hf x hx))
    (fun x hx => UniqueFactorizationMonoid.irreducible_iff_prime.mp (hg x hx)) h

end UniqueFactorizationMonoid

theorem prime_factors_irreducible [CommMonoidWithZero α] {a : α} {f : Multiset α}
    (ha : Irreducible a) (pfa : (∀ b ∈ f, Prime b) ∧ f.prod ~ᵤ a) : ∃ p, a ~ᵤ p ∧ f = {p} := by
  haveI := Classical.decEq α
  refine @Multiset.induction_on _
    (fun g => (g.prod ~ᵤ a) → (∀ b ∈ g, Prime b) → ∃ p, a ~ᵤ p ∧ g = {p}) f ?_ ?_ pfa.2 pfa.1
  · intro h; exact (ha.not_isUnit (associated_one_iff_isUnit.1 (Associated.symm h))).elim
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

-- DISSOLVED: irreducible_iff_prime_of_existsUnique_irreducible_factors

namespace UniqueFactorizationMonoid

open Multiset

variable [CommMonoidWithZero α]

variable [UniqueFactorizationMonoid α]
