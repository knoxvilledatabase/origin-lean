/-
Extracted from RingTheory/UniqueFactorizationDomain/Defs.lean
Genuine: 9 of 21 | Dissolved: 9 | Infrastructure: 3
-/
import Origin.Core
import Mathlib.Algebra.Associated.Basic
import Mathlib.Algebra.BigOperators.Group.Multiset
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Order.WellFounded

/-!
# Unique factorization

## Main Definitions
* `WfDvdMonoid` holds for `Monoid`s for which a strict divisibility relation is
  well-founded.
* `UniqueFactorizationMonoid` holds for `WfDvdMonoid`s where
  `Irreducible` is equivalent to `Prime`
-/

variable {α : Type*}

local infixl:50 " ~ᵤ " => Associated

abbrev WfDvdMonoid (α : Type*) [CommMonoidWithZero α] : Prop :=
  IsWellFounded α DvdNotUnit

theorem wellFounded_dvdNotUnit {α : Type*} [CommMonoidWithZero α] [h : WfDvdMonoid α] :
    WellFounded (DvdNotUnit (α := α)) :=
  h.wf

namespace WfDvdMonoid

variable [CommMonoidWithZero α]

open Associates Nat

variable [WfDvdMonoid α]

-- DISSOLVED: exists_irreducible_factor

-- DISSOLVED: induction_on_irreducible

-- DISSOLVED: exists_factors

-- DISSOLVED: not_unit_iff_exists_factors_eq

theorem isRelPrime_of_no_irreducible_factors {x y : α} (nonzero : ¬(x = 0 ∧ y = 0))
    (H : ∀ z : α, Irreducible z → z ∣ x → ¬z ∣ y) : IsRelPrime x y :=
  isRelPrime_of_no_nonunits_factors nonzero fun _z znu znz zx zy ↦
    have ⟨i, h1, h2⟩ := exists_irreducible_factor znu znz
    H i h1 (h2.trans zx) (h2.trans zy)

end WfDvdMonoid

section Prio

class UniqueFactorizationMonoid (α : Type*) [CancelCommMonoidWithZero α] extends
    IsWellFounded α DvdNotUnit : Prop where
  protected irreducible_iff_prime : ∀ {a : α}, Irreducible a ↔ Prime a

instance (priority := 100) ufm_of_decomposition_of_wfDvdMonoid
    [CancelCommMonoidWithZero α] [WfDvdMonoid α] [DecompositionMonoid α] :
    UniqueFactorizationMonoid α :=
  { ‹WfDvdMonoid α› with irreducible_iff_prime := irreducible_iff_prime }

theorem ufm_of_gcd_of_wfDvdMonoid [CancelCommMonoidWithZero α] [WfDvdMonoid α]
    [DecompositionMonoid α] : UniqueFactorizationMonoid α :=
  ufm_of_decomposition_of_wfDvdMonoid

end Prio

namespace UniqueFactorizationMonoid

variable [CancelCommMonoidWithZero α] [UniqueFactorizationMonoid α]

-- DISSOLVED: exists_prime_factors

-- DISSOLVED: exists_prime_iff

-- DISSOLVED: induction_on_prime

instance : DecompositionMonoid α where
  primal a := by
    obtain rfl | ha := eq_or_ne a 0; · exact isPrimal_zero
    obtain ⟨f, hf, u, rfl⟩ := exists_prime_factors a ha
    exact ((Submonoid.isPrimal α).multiset_prod_mem f (hf · ·|>.isPrimal)).mul u.isUnit.isPrimal

end UniqueFactorizationMonoid

namespace UniqueFactorizationMonoid

variable [CancelCommMonoidWithZero α]

variable [UniqueFactorizationMonoid α]

open Classical in

noncomputable def factors (a : α) : Multiset α :=
  if h : a = 0 then 0 else Classical.choose (UniqueFactorizationMonoid.exists_prime_factors a h)

-- DISSOLVED: factors_prod

@[simp]
theorem factors_zero : factors (0 : α) = 0 := by simp [factors]

-- DISSOLVED: ne_zero_of_mem_factors

theorem dvd_of_mem_factors {p a : α} (h : p ∈ factors a) : p ∣ a :=
  dvd_trans (Multiset.dvd_prod h) (Associated.dvd (factors_prod (ne_zero_of_mem_factors h)))

theorem prime_of_factor {a : α} (x : α) (hx : x ∈ factors a) : Prime x := by
  have ane0 := ne_zero_of_mem_factors hx
  rw [factors, dif_neg ane0] at hx
  exact (Classical.choose_spec (UniqueFactorizationMonoid.exists_prime_factors a ane0)).1 x hx

theorem irreducible_of_factor {a : α} : ∀ x : α, x ∈ factors a → Irreducible x := fun x h =>
  (prime_of_factor x h).irreducible

end UniqueFactorizationMonoid
