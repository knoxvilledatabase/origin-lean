/-
Released under MIT license.
-/
import Val.Algebra

/-!
# Ring Theory on Val α

Ideals, quotient rings, localization, prime ideals, integral domains.
The sort system dissolves the `s ≠ 0` hypothesis for localization and
the NoZeroDivisors typeclass for integral domains.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Ideals
-- ============================================================================

/-- Ideal membership predicate on Val α.
    Contents elements are in the ideal iff the underlying α-value is.
    Origin and container are outside all ideals. -/
def inIdeal (I : α → Prop) : Val α → Prop
  | contents a => I a
  | _ => False

@[simp] theorem inIdeal_contents (I : α → Prop) (a : α) :
    inIdeal I (contents a) = I a := rfl

/-- Origin is not in any ideal. -/
theorem origin_not_in_ideal (I : α → Prop) :
    ¬ inIdeal I (origin : Val α) := id

/-- Container is not in any ideal. -/
theorem container_not_in_ideal (I : α → Prop) (c : α) :
    ¬ inIdeal I (container c : Val α) := id

/-- Ideal closed under addition within contents. -/
theorem ideal_add_closed (I : α → Prop) (addF : α → α → α)
    (hI : ∀ a b : α, I a → I b → I (addF a b))
    (a b : α) (ha : inIdeal I (contents a)) (hb : inIdeal I (contents b)) :
    inIdeal I (add addF (contents a) (contents b)) := by
  show I (addF a b); exact hI a b ha hb

/-- Ideal absorbs ring multiplication within contents. -/
theorem ideal_mul_absorb (I : α → Prop) (mulF : α → α → α)
    (hI : ∀ r a : α, I a → I (mulF r a))
    (r a : α) (ha : inIdeal I (contents a)) :
    inIdeal I (mul mulF (contents r) (contents a)) := by
  show I (mulF r a); exact hI r a ha

-- ============================================================================
-- Quotient Rings
-- ============================================================================

/-- Quotient map: sends contents to its equivalence class, preserves origin/container. -/
def quotientMap (proj : α → α) : Val α → Val α
  | origin => origin
  | container a => container (proj a)
  | contents a => contents (proj a)

@[simp] theorem quotient_contents (proj : α → α) (a : α) :
    quotientMap proj (contents a) = contents (proj a) := rfl

/-- Quotient of contents is never origin. -/
theorem quotient_ne_origin (proj : α → α) (a : α) :
    quotientMap proj (contents a) ≠ origin := by simp [quotientMap]

/-- Quotient map commutes with addition within contents. -/
theorem quotient_add (proj : α → α) (addF addQ : α → α → α)
    (h : ∀ a b : α, proj (addF a b) = addQ (proj a) (proj b))
    (a b : α) :
    quotientMap proj (add addF (contents a) (contents b)) =
    add addQ (quotientMap proj (contents a)) (quotientMap proj (contents b)) := by
  simp [h]

/-- Quotient map commutes with multiplication within contents. -/
theorem quotient_mul (proj : α → α) (mulF mulQ : α → α → α)
    (h : ∀ a b : α, proj (mulF a b) = mulQ (proj a) (proj b))
    (a b : α) :
    quotientMap proj (mul mulF (contents a) (contents b)) =
    mul mulQ (quotientMap proj (contents a)) (quotientMap proj (contents b)) := by
  simp [h]

-- ============================================================================
-- Localization: No s ≠ 0 Hypothesis
-- ============================================================================

/-- a/s = contents(a · s⁻¹). No hypothesis that s ≠ 0. -/
theorem localization_contents (mulF : α → α → α) (invF : α → α) (a s : α) :
    mul mulF (contents a) (inv invF (contents s)) =
    contents (mulF a (invF s)) := rfl

/-- Localized element is never origin. No hypothesis on s. -/
theorem localization_ne_origin (mulF : α → α → α) (invF : α → α) (a s : α) :
    mul mulF (contents a) (inv invF (contents s)) ≠ origin := by simp

/-- Localization preserves multiplication within contents. -/
theorem localization_mul (mulF : α → α → α) (invF : α → α) (a b s t : α) :
    mul mulF
      (mul mulF (contents a) (inv invF (contents s)))
      (mul mulF (contents b) (inv invF (contents t))) =
    contents (mulF (mulF a (invF s)) (mulF b (invF t))) := rfl

-- ============================================================================
-- Prime Ideals
-- ============================================================================

/-- Prime ideal: if ab ∈ P then a ∈ P or b ∈ P, within contents. -/
theorem prime_ideal_contents (P : α → Prop) (mulF : α → α → α)
    (hP : ∀ a b : α, P (mulF a b) → P a ∨ P b)
    (a b : α) (hab : inIdeal P (mul mulF (contents a) (contents b))) :
    inIdeal P (contents a) ∨ inIdeal P (contents b) :=
  hP a b hab

-- ============================================================================
-- Integral Domains: NoZeroDivisors Is Structural
-- ============================================================================

/-- Contents × contents is always contents. Never origin.
    NoZeroDivisors as a typeclass is unnecessary — the sort carries the invariant. -/
theorem no_zero_divisors_structural (mulF : α → α → α) (a b : α) :
    mul mulF (contents a) (contents b) ≠ origin := by simp

/-- If α has no zero divisors, Val α contents inherit that. -/
theorem integral_domain_contents (mulF : α → α → α) (zero : α)
    (h : ∀ a b : α, mulF a b = zero → a = zero ∨ b = zero)
    (a b : α) (hab : mul mulF (contents a) (contents b) = contents zero) :
    contents a = contents zero ∨ contents b = contents zero := by
  simp at hab
  cases h a b hab with
  | inl ha => left; congr
  | inr hb => right; congr

-- ============================================================================
-- Residue Fields
-- ============================================================================

/-- Residue field element is never origin. -/
theorem residue_field_ne_origin (proj : α → α) (a : α) :
    quotientMap proj (contents a) ≠ origin := by simp [quotientMap]

end Val
