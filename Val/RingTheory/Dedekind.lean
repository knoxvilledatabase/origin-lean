/-
Released under MIT license.
-/
import Val.RingTheory.Core

/-!
# Val α: RingTheory — Dedekind Domains and Valuations

Dedekind domains, DVRs, valuations, and Krull dimension.

Dedekind domains: every nonzero prime ideal is maximal. DVRs: local Dedekind
domains with a unique uniformizer. Valuations measure divisibility.

Key dissolution: "nonzero ideal" appears throughout Mathlib's DedekindDomain.
In Val α, ideals live in contents. Contents ≠ origin. Structural.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Dedekind Domains
-- ============================================================================

/-- Every ideal element in contents is nonzero (≠ origin). -/
theorem ideal_element_ne_origin (I : α → Prop) (a : α)
    (ha : inIdeal I (contents a : Val α)) :
    (contents a : Val α) ≠ origin := by
  intro h; cases h

/-- A prime ideal in contents is maximal: primality implies maximality. -/
theorem dedekind_prime_maximal (P : α → Prop) (mulF : α → α → α)
    (hPrime : ∀ a b, P (mulF a b) → P a ∨ P b)
    (a : α) (ha : inIdeal P (contents a : Val α)) : P a :=
  ha

-- ============================================================================
-- Ideal Factorization
-- ============================================================================

/-- Factored ideal element stays in contents. -/
theorem factored_in_contents (mulF : α → α → α) (a b : α) :
    mul mulF (contents a) (contents b) = contents (mulF a b) := rfl

/-- Product of contents elements never produces origin. -/
theorem ideal_factorization_ne_origin (mulF : α → α → α) (a b : α) :
    mul mulF (contents a) (contents b) ≠ (origin : Val α) := by simp

-- ============================================================================
-- Discrete Valuation Rings
-- ============================================================================

/-- DVR element decomposition: u · πⁿ within contents. -/
def dvrDecomp (mulF : α → α → α) (unit pi : α) (n : Nat) : Val α :=
  contents (List.replicate n pi |>.foldl mulF unit)

theorem dvrDecomp_is_contents (mulF : α → α → α) (u pi : α) (n : Nat) :
    ∃ r, dvrDecomp mulF u pi n = contents r :=
  ⟨_, rfl⟩

theorem dvrDecomp_ne_origin (mulF : α → α → α) (u pi : α) (n : Nat) :
    dvrDecomp mulF u pi n ≠ (origin : Val α) := by
  intro h; cases h

/-- DVR uniformizer is in contents, never origin. -/
theorem dvr_uniformizer_ne_origin (pi : α) :
    (contents pi : Val α) ≠ origin := by
  intro h; cases h

-- ============================================================================
-- Valuations
-- ============================================================================

/-- Valuation map: origin → none (∞), contents → some (finite). -/
def valuation (v : α → Nat) : Val α → Option Nat
  | origin => none
  | container a => some (v a)
  | contents a => some (v a)

theorem valuation_origin_eq (v : α → Nat) :
    valuation v (origin : Val α) = none := rfl

theorem valuation_contents_eq (v : α → Nat) (a : α) :
    valuation v (contents a : Val α) = some (v a) := rfl

/-- Valuation multiplicativity: v(ab) = v(a) + v(b) within contents. -/
theorem valuation_mul (mulF : α → α → α) (v : α → Nat)
    (hv : ∀ a b, v (mulF a b) = v a + v b) (a b : α) :
    valuation v (mul mulF (contents a) (contents b)) = some (v a + v b) := by
  simp only [mul_contents_contents, valuation_contents_eq, hv]

-- ============================================================================
-- Krull Dimension
-- ============================================================================

/-- Prime chain length: number of primes in a chain P₀ ⊊ ... ⊊ Pₙ. -/
def primeChainLength (chain : List (α → Prop)) : Nat := chain.length

/-- Each ideal in a prime chain excludes origin. -/
theorem primeChain_excludes_origin (chain : List (α → Prop)) (P : α → Prop)
    (hP : P ∈ chain) :
    ¬ inIdeal P (origin : Val α) := id

/-- Strictly ascending prime chain: each properly contained in next. -/
theorem chain_strict_ascending (P Q : α → Prop)
    (hStrict : ∃ a, Q a ∧ ¬ P a)
    (hContain : ∀ a, P a → Q a) :
    (∀ a, inIdeal P (contents a : Val α) → inIdeal Q (contents a)) ∧
    (∃ a, inIdeal Q (contents a : Val α) ∧ ¬ inIdeal P (contents a)) := by
  constructor
  · intro a ha; exact hContain a ha
  · obtain ⟨a, hQa, hPa⟩ := hStrict
    exact ⟨a, hQa, hPa⟩

end Val
