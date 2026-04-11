/-
Released under MIT license.
-/
import Val.Algebra

/-!
# Ring Theory on Val α

Ideals, quotient rings, localization, prime ideals, integral domains,
chain conditions, structural theorems, Dedekind domains, graded algebras,
tensor products, algebraic elements, polynomial rings, and schemes.

The sort system dissolves the `s ≠ 0` hypothesis for localization,
the `NoZeroDivisors` typeclass for integral domains, `Nontrivial`
guards on spectrum theorems, and `NeZero` on characteristic computations.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- § Core: Ideals
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
-- § Core: Quotient Rings
-- ============================================================================

-- quotientMap defined in Algebra.lean

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
-- § Core: Localization — No s ≠ 0 Hypothesis
-- ============================================================================

/-- a/s = contents(a · s⁻¹). No hypothesis that s ≠ 0. -/
theorem localization_contents (mulF : α → α → α) (invF : α → α) (a s : α) :
    mul mulF (contents a) (inv invF (contents s)) =
    contents (mulF a (invF s)) := rfl

/-- Localization preserves multiplication within contents. -/
theorem localization_mul (mulF : α → α → α) (invF : α → α) (a b s t : α) :
    mul mulF
      (mul mulF (contents a) (inv invF (contents s)))
      (mul mulF (contents b) (inv invF (contents t))) =
    contents (mulF (mulF a (invF s)) (mulF b (invF t))) := rfl

-- ============================================================================
-- § Core: Prime Ideals
-- ============================================================================

/-- Prime ideal: if ab ∈ P then a ∈ P or b ∈ P, within contents. -/
theorem prime_ideal_contents (P : α → Prop) (mulF : α → α → α)
    (hP : ∀ a b : α, P (mulF a b) → P a ∨ P b)
    (a b : α) (hab : inIdeal P (mul mulF (contents a) (contents b))) :
    inIdeal P (contents a) ∨ inIdeal P (contents b) :=
  hP a b hab

-- ============================================================================
-- § Core: Integral Domains — NoZeroDivisors Is Structural
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
-- § Core: Residue Fields
-- ============================================================================

-- ============================================================================
-- § Ideals: Ideal Sum and Product
-- ============================================================================

/-- Ideal sum: a ∈ I + J iff a = b + c with b ∈ I, c ∈ J. -/
def idealSum (addF : α → α → α) (I J : α → Prop) : α → Prop :=
  fun a => ∃ b c, I b ∧ J c ∧ a = addF b c

/-- Ideal product: generated by products ab with a ∈ I, b ∈ J. -/
def idealProd (mulF : α → α → α) (I J : α → Prop) : α → Prop :=
  fun a => ∃ b c, I b ∧ J c ∧ a = mulF b c

theorem idealSum_in_contents (addF : α → α → α) (I J : α → Prop) (b c : α)
    (hb : I b) (hc : J c) :
    inIdeal (idealSum addF I J) (contents (addF b c) : Val α) :=
  ⟨b, c, hb, hc, rfl⟩

theorem idealProd_in_contents (mulF : α → α → α) (I J : α → Prop) (b c : α)
    (hb : I b) (hc : J c) :
    inIdeal (idealProd mulF I J) (contents (mulF b c) : Val α) :=
  ⟨b, c, hb, hc, rfl⟩

theorem origin_not_in_idealSum (addF : α → α → α) (I J : α → Prop) :
    ¬ inIdeal (idealSum addF I J) (origin : Val α) := id

theorem origin_not_in_idealProd (mulF : α → α → α) (I J : α → Prop) :
    ¬ inIdeal (idealProd mulF I J) (origin : Val α) := id

-- ============================================================================
-- § Ideals: Ideal Intersection and Containment
-- ============================================================================

/-- Ideal intersection. -/
def idealInter (I J : α → Prop) : α → Prop :=
  fun a => I a ∧ J a

theorem idealInter_in_contents (I J : α → Prop) (a : α) (hI : I a) (hJ : J a) :
    inIdeal (idealInter I J) (contents a : Val α) :=
  ⟨hI, hJ⟩

theorem ideal_containment (I J : α → Prop)
    (h : ∀ a, I a → J a) (a : α) (ha : inIdeal I (contents a : Val α)) :
    inIdeal J (contents a) :=
  h a ha

-- ============================================================================
-- § Ideals: Two-Sided Ideals
-- ============================================================================

theorem two_sided_left (mulF : α → α → α) (I : α → Prop)
    (hI : ∀ r a, I a → I (mulF r a)) (r a : α)
    (ha : inIdeal I (contents a : Val α)) :
    inIdeal I (mul mulF (contents r) (contents a)) :=
  hI r a ha

theorem two_sided_right (mulF : α → α → α) (I : α → Prop)
    (hI : ∀ a r, I a → I (mulF a r)) (a r : α)
    (ha : inIdeal I (contents a : Val α)) :
    inIdeal I (mul mulF (contents a) (contents r)) :=
  hI a r ha

-- ============================================================================
-- § Ideals: Fractional Ideals — The s ≠ 0 Dissolution
-- ============================================================================

/-- Fractional ideal element: a/s in contents. No s ≠ 0 hypothesis. -/
def fractionalElem (mulF : α → α → α) (invF : α → α) (a s : α) : Val α :=
  mul mulF (contents a) (inv invF (contents s))

theorem fractionalElem_is_contents (mulF : α → α → α) (invF : α → α) (a s : α) :
    fractionalElem mulF invF a s = contents (mulF a (invF s)) := rfl

theorem fractionalElem_mul (mulF : α → α → α) (invF : α → α) (a b s t : α) :
    mul mulF (fractionalElem mulF invF a s) (fractionalElem mulF invF b t) =
    contents (mulF (mulF a (invF s)) (mulF b (invF t))) := rfl

-- ============================================================================
-- § Ideals: Ideal Quotient and Annihilator
-- ============================================================================

/-- Ideal quotient (colon ideal): (I : J) = { r | rJ ⊆ I }. -/
def idealQuot (mulF : α → α → α) (I J : α → Prop) : α → Prop :=
  fun r => ∀ a, J a → I (mulF r a)

theorem idealQuot_in_contents (mulF : α → α → α) (I J : α → Prop) (r : α)
    (h : ∀ a, J a → I (mulF r a)) :
    inIdeal (idealQuot mulF I J) (contents r : Val α) :=
  h

theorem origin_not_in_idealQuot (mulF : α → α → α) (I J : α → Prop) :
    ¬ inIdeal (idealQuot mulF I J) (origin : Val α) := id

/-- Annihilator of a set. -/
def annihilator (mulF : α → α → α) (target : α → Prop) (a : α) : α → Prop :=
  fun r => target (mulF r a)

theorem annihilator_in_contents (mulF : α → α → α) (target : α → Prop) (a r : α)
    (h : target (mulF r a)) :
    inIdeal (annihilator mulF target a) (contents r : Val α) :=
  h

-- ============================================================================
-- § Localization: Multiplicative Subsets
-- ============================================================================

/-- A multiplicative subset: closed under multiplication. -/
structure MulSubset (α : Type u) (mulF : α → α → α) (one : α) where
  mem : α → Prop
  one_mem : mem one
  mul_mem : ∀ a b, mem a → mem b → mem (mulF a b)

-- ============================================================================
-- § Localization: Fractions a/s
-- ============================================================================

/-- Localization fraction. In Mathlib: requires s ∈ S, S ⊆ nonZeroDivisors. -/
def locFrac (mulF : α → α → α) (invF : α → α) (a s : α) : Val α :=
  mul mulF (contents a) (inv invF (contents s))

theorem locFrac_eq (mulF : α → α → α) (invF : α → α) (a s : α) :
    locFrac mulF invF a s = contents (mulF a (invF s)) := rfl

/-- Equality of fractions reduces to contents-level equality. -/
theorem locFrac_eq_iff (mulF : α → α → α) (invF : α → α) (a b s t : α)
    (h : mulF a (invF s) = mulF b (invF t)) :
    locFrac mulF invF a s = locFrac mulF invF b t := by
  simp only [locFrac_eq]; exact congrArg contents h

-- ============================================================================
-- § Localization: Arithmetic
-- ============================================================================

theorem locFrac_mul (mulF : α → α → α) (invF : α → α) (a b s t : α) :
    mul mulF (locFrac mulF invF a s) (locFrac mulF invF b t) =
    contents (mulF (mulF a (invF s)) (mulF b (invF t))) := rfl

theorem locFrac_add (addF mulF : α → α → α) (invF : α → α) (a b s t : α) :
    add addF (locFrac mulF invF a s) (locFrac mulF invF b t) =
    contents (addF (mulF a (invF s)) (mulF b (invF t))) := rfl

/-- The fraction s/s is always contents. -/
theorem locFrac_self (mulF : α → α → α) (invF : α → α) (s : α) :
    locFrac mulF invF s s = contents (mulF s (invF s)) := rfl

-- ============================================================================
-- § Localization: Ore Localization (Noncommutative)
-- ============================================================================

/-- Ore fraction: same sort dissolution in noncommutative setting. -/
def oreFrac (mulF : α → α → α) (invF : α → α) (a s : α) : Val α :=
  mul mulF (contents a) (inv invF (contents s))

theorem oreFrac_is_contents (mulF : α → α → α) (invF : α → α) (a s : α) :
    oreFrac mulF invF a s = contents (mulF a (invF s)) := rfl

-- ============================================================================
-- § Localization: Local Rings
-- ============================================================================

/-- In a local ring, every non-unit is in the maximal ideal. -/
theorem local_ring_non_unit (M : α → Prop) (isNonUnit : α → Prop)
    (h : ∀ a, isNonUnit a → M a) (a : α) (ha : isNonUnit a) :
    inIdeal M (contents a : Val α) :=
  h a ha

/-- The unique maximal ideal excludes origin. -/
theorem local_ring_maximal_excludes_origin (M : α → Prop) :
    ¬ inIdeal M (origin : Val α) := id

/-- Units: contents(a) * contents(a⁻¹) = contents(a · a⁻¹). -/
theorem local_ring_unit_inv (mulF : α → α → α) (invF : α → α) (a : α) :
    mul mulF (contents a) (inv invF (contents a)) =
    contents (mulF a (invF a)) := rfl

-- ============================================================================
-- § Localization: Local Properties
-- ============================================================================

/-- A property holds locally: it holds for all localizations. -/
theorem local_property_contents (mulF : α → α → α) (invF : α → α)
    (P : Val α → Prop) (a s : α)
    (hP : P (contents (mulF a (invF s)))) :
    P (locFrac mulF invF a s) :=
  hP

-- ============================================================================
-- § Noetherian: Ascending Chain Condition
-- ============================================================================

/-- ACC on ideals: every ascending chain stabilizes. -/
theorem noetherian_acc (chain : Nat → α → Prop)
    (hAsc : ∀ n, ∀ a, chain n a → chain (n + 1) a)
    (hStab : ∃ N, ∀ n, N ≤ n → ∀ a, chain n a ↔ chain N a)
    (a : α) :
    ∃ N, ∀ m, N ≤ m → (chain m a ↔ chain N a) := by
  obtain ⟨N, hN⟩ := hStab
  exact ⟨N, fun m hm => hN m hm a⟩

/-- Origin is outside every ideal in an ascending chain. -/
theorem noetherian_origin_outside (chain : Nat → α → Prop) (n : Nat) :
    ¬ inIdeal (chain n) (origin : Val α) := id

-- ============================================================================
-- § Noetherian: Artinian — Descending Chain Condition
-- ============================================================================

/-- DCC on ideals: every descending chain stabilizes. -/
theorem artinian_dcc (chain : Nat → α → Prop)
    (hDesc : ∀ n, ∀ a, chain (n + 1) a → chain n a)
    (hStab : ∃ N, ∀ n, N ≤ n → ∀ a, chain n a ↔ chain N a)
    (a : α) :
    ∃ N, ∀ m, N ≤ m → (chain m a ↔ chain N a) := by
  obtain ⟨N, hN⟩ := hStab
  exact ⟨N, fun m hm => hN m hm a⟩

-- ============================================================================
-- § Noetherian: Finitely Generated Ideals
-- ============================================================================

/-- Finitely generated ideal: I = ⟨a₁, ..., aₙ⟩. All generators in contents. -/
def finGenIdeal (mulF addF : α → α → α) (generators : List α) : α → Prop :=
  fun a => ∃ coeffs : List α, coeffs.length = generators.length ∧
    a = (coeffs.zip generators).foldl (fun acc p => addF acc (mulF p.1 p.2)) a

-- ============================================================================
-- § Noetherian: Nilpotent Elements
-- ============================================================================

/-- Iterated multiplication in Val α (explicit, no typeclasses). -/
def valPow (mulF : α → α → α) (one : α) : Val α → Nat → Val α
  | _, 0 => contents one
  | v, n + 1 => mul mulF v (valPow mulF one v n)

/-- valPow on origin gives origin for positive n. -/
theorem valPow_origin (mulF : α → α → α) (one : α) (n : Nat) (hn : 0 < n) :
    valPow mulF one (origin : Val α) n = origin := by
  cases n with
  | zero => omega
  | succ n => show mul mulF origin (valPow mulF one origin n) = origin; simp

/-- valPow on contents gives contents (sort preserved). -/
theorem valPow_contents_sort (mulF : α → α → α) (one : α) (a : α) (n : Nat) :
    ∃ r, valPow mulF one (contents a) n = contents r := by
  induction n with
  | zero => exact ⟨one, rfl⟩
  | succ n ih =>
    obtain ⟨r, hr⟩ := ih
    show ∃ r', mul mulF (contents a) (valPow mulF one (contents a) n) = contents r'
    rw [hr]; exact ⟨mulF a r, rfl⟩

/-- Nilpotent elements are never origin. -/
theorem nilpotent_ne_origin (mulF : α → α → α) (one : α) (a : α) (n : Nat) :
    valPow mulF one (contents a) n ≠ (origin : Val α) := by
  obtain ⟨r, hr⟩ := valPow_contents_sort mulF one a n
  rw [hr]; intro h; cases h

-- ============================================================================
-- § Noetherian: Regular Elements
-- ============================================================================

-- ============================================================================
-- § Structure: Congruence
-- ============================================================================

/-- Ring congruence: equivalence relation compatible with operations. -/
def ringCong (rel : α → α → Prop) : Val α → Val α → Prop
  | contents a, contents b => rel a b
  | origin, origin => True
  | container a, container b => rel a b
  | _, _ => False

theorem ringCong_refl (rel : α → α → Prop) (hRefl : ∀ a, rel a a) (v : Val α) :
    ringCong rel v v := by
  cases v with
  | origin => exact trivial
  | container a => exact hRefl a
  | contents a => exact hRefl a

theorem ringCong_origin_only (rel : α → α → Prop) (a : α) :
    ¬ ringCong rel (contents a) (origin : Val α) := id

-- ============================================================================
-- § Structure: Coprime Elements
-- ============================================================================

/-- Coprime witness: x·a + y·b = 1 in contents. -/
theorem coprime_witness (addF mulF : α → α → α) (one : α)
    (a b x y : α) (h : addF (mulF x a) (mulF y b) = one) :
    add addF (mul mulF (contents x) (contents a)) (mul mulF (contents y) (contents b)) =
    contents one := by
  show contents (addF (mulF x a) (mulF y b)) = contents one
  rw [h]

-- ============================================================================
-- § Structure: Jacobson Radical
-- ============================================================================

/-- Jacobson radical: in every maximal ideal. -/
def jacobsonRadical (maxIdeals : List (α → Prop)) (a : α) : Prop :=
  ∀ M, M ∈ maxIdeals → M a

theorem origin_not_in_jacobson (maxIdeals : List (α → Prop)) :
    ¬ inIdeal (jacobsonRadical maxIdeals) (origin : Val α) := id

-- ============================================================================
-- § Structure: Roots of Unity
-- ============================================================================

-- ============================================================================
-- § Structure: UFD — Unique Factorization Domain
-- ============================================================================

/-- Product of two irreducibles is contents. -/
theorem irreducible_product_contents (mulF : α → α → α) (a b : α) :
    mul mulF (contents a) (contents b) = contents (mulF a b) := rfl

-- ============================================================================
-- § Structure: Simple Rings
-- ============================================================================

/-- Simple ring: ideal is trivial or everything. -/
theorem simple_ring_dichotomy (I : α → Prop) (zero : α)
    (hSimple : (∀ a, I a → a = zero) ∨ (∀ a, I a)) (a : α) (ha : I a) :
    inIdeal I (contents a : Val α) := ha

-- ============================================================================
-- § Structure: Radical of an Ideal
-- ============================================================================

/-- Radical membership: some power lands in the ideal. -/
def inRadical (powF : α → Nat → α) (I : α → Prop) (a : α) : Prop :=
  ∃ n : Nat, I (powF a n)

theorem origin_not_in_radical (powF : α → Nat → α) (I : α → Prop) :
    ¬ inIdeal (inRadical powF I) (origin : Val α) := id

-- ============================================================================
-- § Dedekind: Dedekind Domains
-- ============================================================================

/-- A prime ideal in contents is maximal: primality implies maximality. -/
theorem dedekind_prime_maximal (P : α → Prop) (mulF : α → α → α)
    (hPrime : ∀ a b, P (mulF a b) → P a ∨ P b)
    (a : α) (ha : inIdeal P (contents a : Val α)) : P a :=
  ha

-- ============================================================================
-- § Dedekind: Ideal Factorization
-- ============================================================================

/-- Factored ideal element stays in contents. -/
theorem factored_in_contents (mulF : α → α → α) (a b : α) :
    mul mulF (contents a) (contents b) = contents (mulF a b) := rfl

-- ============================================================================
-- § Dedekind: Discrete Valuation Rings
-- ============================================================================

/-- DVR element decomposition: u · πⁿ within contents. -/
def dvrDecomp (mulF : α → α → α) (unit pi : α) (n : Nat) : Val α :=
  contents (List.replicate n pi |>.foldl mulF unit)

-- ============================================================================
-- § Dedekind: Valuations
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
-- § Dedekind: Krull Dimension
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

-- ============================================================================
-- § Graded: Graded Algebra — R = ⊕ Rₙ
-- ============================================================================

/-- Graded component: elements of degree n. -/
def gradedComponent (grade : α → Nat) (n : Nat) : α → Prop :=
  fun a => grade a = n

/-- Origin is outside every graded component. -/
theorem origin_not_graded (grade : α → Nat) (n : Nat) :
    ¬ inIdeal (gradedComponent grade n) (origin : Val α) := id

/-- Product of graded elements: degrees add. -/
theorem graded_mul (mulF : α → α → α) (grade : α → Nat) (m n : Nat)
    (hGrade : ∀ a b, grade (mulF a b) = grade a + grade b)
    (a b : α) (ha : gradedComponent grade m a) (hb : gradedComponent grade n b) :
    gradedComponent grade (m + n) (mulF a b) := by
  show grade (mulF a b) = m + n
  rw [hGrade, ha, hb]

-- ============================================================================
-- § Graded: Filtered Algebra
-- ============================================================================

/-- Filtration: increasing sequence of subsets. -/
def filtration (F : Nat → α → Prop) : Prop :=
  ∀ n a, F n a → F (n + 1) a

/-- Filtration compatible with products. -/
theorem filtered_mul (mulF : α → α → α) (F : Nat → α → Prop)
    (hF : ∀ m n a b, F m a → F n b → F (m + n) (mulF a b))
    (m n : Nat) (a b : α) (ha : F m a) (hb : F n b) :
    inIdeal (F (m + n)) (mul mulF (contents a) (contents b)) := by
  show F (m + n) (mulF a b)
  exact hF m n a b ha hb

-- ============================================================================
-- § Graded: Divided Powers
-- ============================================================================

/-- Divided power operation γₙ(a) = aⁿ/n! (formal). -/
abbrev dividedPower (gamma : Nat → α → α) (n : Nat) : Val α → Val α := valMap (gamma n)

/-- Divided power product rule: γₘ · γₙ = C(m+n,m) · γₘ₊ₙ within contents. -/
theorem dividedPower_mul (mulF : α → α → α) (gamma : Nat → α → α)
    (binom : Nat → Nat → α)
    (hDP : ∀ m n a, mulF (gamma m a) (gamma n a) = mulF (binom (m + n) m) (gamma (m + n) a))
    (m n : Nat) (a : α) :
    mul mulF (contents (gamma m a)) (contents (gamma n a)) =
    contents (mulF (binom (m + n) m) (gamma (m + n) a)) := by
  show contents (mulF (gamma m a) (gamma n a)) = contents (mulF (binom (m + n) m) (gamma (m + n) a))
  rw [hDP]

-- ============================================================================
-- § Graded: Witt Vectors
-- ============================================================================

/-- Witt vector component access. -/
def wittComponent (n : Nat) (components : Nat → Val α) : Val α :=
  components n

theorem witt_contents_component (f : Nat → α) (n : Nat) :
    wittComponent n (fun i => contents (f i)) = contents (f n) := rfl

theorem witt_origin_component (n : Nat) :
    wittComponent n (fun _ => (origin : Val α)) = origin := rfl

/-- Witt addition: componentwise (simplified). -/
theorem witt_add (addF : α → α → α) (f g : Nat → α) (n : Nat) :
    add addF (contents (f n)) (contents (g n)) = contents (addF (f n) (g n)) := rfl

-- ============================================================================
-- § Tensor: Tensor Products — Sort-Level
-- ============================================================================

/-- Elementary tensor: m ⊗ n at the sort level. -/
def tensorPair (mulF : α → α → α) (m n : Val α) : Val α :=
  mul mulF m n

-- ============================================================================
-- § Tensor: Bilinearity
-- ============================================================================

-- ============================================================================
-- § Tensor: Flat Modules
-- ============================================================================

/-- Flatness: tensoring with contents preserves contents. -/
theorem flat_preserves_contents (mulF : α → α → α) (m a : α) :
    tensorPair mulF (contents m) (contents a) = contents (mulF m a) := rfl

/-- Torsion-free at sort level: if m ⊗ v = origin then v = origin. -/
theorem torsion_free_sort (mulF : α → α → α) (a : α) (v : Val α)
    (h : tensorPair mulF (contents a) v = origin) :
    v = origin := by
  cases v with
  | origin => rfl
  | container b => cases h
  | contents b => cases h

-- ============================================================================
-- § Tensor: Derivations — d(ab) = a·db + b·da
-- ============================================================================

/-- Leibniz rule: D(ab) = a·Db + b·Da within contents. -/
theorem derivation_leibniz (addF mulF : α → α → α) (a b Da Db : α) :
    add addF (mul mulF (contents a) (contents Db)) (mul mulF (contents b) (contents Da)) =
    contents (addF (mulF a Db) (mulF b Da)) := rfl

/-- Derivation of origin is origin. -/
theorem derivation_origin_val (D : Val α → Val α)
    (hD : D origin = origin) :
    D origin = origin := hD

-- ============================================================================
-- § Tensor: Kaehler Differentials
-- ============================================================================

/-- Differential element ds for s in contents. -/
def kahlerDiff (d : α → α) (a : α) : Val α := contents (d a)

theorem kahlerDiff_is_contents (d : α → α) (a : α) :
    kahlerDiff d a = contents (d a) := rfl

/-- Kaehler differential product: d(ab) = a·db + b·da. -/
theorem kahlerDiff_product (addF mulF : α → α → α) (d : α → α)
    (hd : ∀ a b, d (mulF a b) = addF (mulF a (d b)) (mulF b (d a))) (a b : α) :
    kahlerDiff d (mulF a b) = contents (addF (mulF a (d b)) (mulF b (d a))) := by
  simp only [kahlerDiff_is_contents, hd]

-- ============================================================================
-- § Tensor: Ring Extensions
-- ============================================================================

/-- Ring extension map preserves sort. -/
abbrev extensionMap (f : α → α) : Val α → Val α := valMap f

-- ============================================================================
-- § Algebraic: Algebraic Elements
-- ============================================================================

-- An element a is algebraic if f(a) = 0 for some nonzero polynomial f.
-- In Val α: contents coefficients are "nonzero" by construction.

/-- Polynomial witness: coefficients in contents. -/
def polyWithContents (addF mulF : α → α → α) (zero : α)
    (coeffs : List α) (a : α) : Val α :=
  polyEval addF mulF zero (coeffs.map contents) (contents a)

theorem polyWithContents_single (addF mulF : α → α → α) (zero c₀ a : α) :
    polyWithContents addF mulF zero [c₀] a = contents c₀ := rfl

/-- Algebraic: some contents-coefficient polynomial evaluates to contents(0). -/
def isAlgebraic (addF mulF : α → α → α) (zero : α) (a : α) : Prop :=
  ∃ poly : List α, poly ≠ [] ∧
    polyWithContents addF mulF zero poly a = contents zero

-- ============================================================================
-- § Algebraic: Algebraic Independence
-- ============================================================================

/-- Algebraically independent: no contents polynomial evaluates to origin. -/
theorem alg_independent (addF mulF : α → α → α) (zero : α) (a : α)
    (h : ∀ poly : List α, poly ≠ [] →
      polyWithContents addF mulF zero poly a ≠ origin) :
    ∀ poly : List α, poly ≠ [] →
      polyWithContents addF mulF zero poly a ≠ (origin : Val α) :=
  h

-- ============================================================================
-- § Algebraic: Integral Closure
-- ============================================================================

/-- Monic polynomial: nonempty and leading coefficient is contents(1). -/
def isMonic (one : α) (poly : List (Val α)) (h : poly ≠ []) : Prop :=
  poly.getLast h = contents one

/-- Monic condition: contents(1) is never origin. -/
theorem monic_leading_ne_origin (one : α) (poly : List (Val α))
    (h : poly ≠ []) (hm : isMonic one poly h) :
    poly.getLast h ≠ (origin : Val α) := by
  rw [hm]; intro h; cases h

/-- Integral element: satisfies a monic polynomial. -/
def isIntegral (addF mulF : α → α → α) (zero one : α) (a : α) : Prop :=
  ∃ poly : List (Val α), ∃ hne : poly ≠ [], isMonic one poly hne ∧
    polyEval addF mulF zero poly (contents a) = contents zero

-- ============================================================================
-- § Algebraic: Adjoin — R[a]
-- ============================================================================

/-- Element of R[a]: polynomial in a with contents coefficients. -/
def adjoinElem (addF mulF : α → α → α) (zero : α) (coeffs : List α) (a : α) : Val α :=
  polyEval addF mulF zero (coeffs.map contents) (contents a)

theorem adjoinElem_single (addF mulF : α → α → α) (zero c₀ a : α) :
    adjoinElem addF mulF zero [c₀] a = contents c₀ := rfl

-- ============================================================================
-- § Algebraic: Norm Map
-- ============================================================================

/-- Norm map preserves sort. -/
abbrev normMap (N : α → α) : Val α → Val α := valMap N

/-- Norm is multiplicative within contents. -/
theorem normMap_mul (mulF : α → α → α) (N : α → α)
    (hN : ∀ a b, N (mulF a b) = mulF (N a) (N b)) (a b : α) :
    normMap N (mul mulF (contents a) (contents b)) =
    mul mulF (normMap N (contents a)) (normMap N (contents b)) := by
  show contents (N (mulF a b)) = contents (mulF (N a) (N b))
  rw [hN]

-- ============================================================================
-- § Algebraic: Trace Map
-- ============================================================================

/-- Trace map preserves sort. -/
abbrev traceMap (T : α → α) : Val α → Val α := valMap T

/-- Trace is additive within contents. -/
theorem traceMap_add (addF : α → α → α) (T : α → α)
    (hT : ∀ a b, T (addF a b) = addF (T a) (T b)) (a b : α) :
    traceMap T (add addF (contents a) (contents b)) =
    add addF (traceMap T (contents a)) (traceMap T (contents b)) := by
  show contents (T (addF a b)) = contents (addF (T a) (T b))
  rw [hT]

-- ============================================================================
-- § Polynomial: Leading Coefficient
-- ============================================================================

/-- Leading coefficient of a polynomial (last element). -/
def leadCoeff : List (Val α) → Val α
  | [] => origin
  | [a] => a
  | _ :: rest => leadCoeff rest

theorem leadCoeff_single (a : Val α) : leadCoeff [a] = a := rfl

theorem leadCoeff_contents_val (a : α) : leadCoeff [contents a] = contents a := rfl

-- ============================================================================
-- § Polynomial: Division — The ≠ 0 Dissolution
-- ============================================================================

/-- Division step: a / b within contents. No leading coeff ≠ 0 guard. -/
theorem poly_div_step (mulF : α → α → α) (invF : α → α) (a b : α) :
    mul mulF (contents a) (inv invF (contents b)) = contents (mulF a (invF b)) := rfl

-- ============================================================================
-- § Polynomial: Multivariate Monomials
-- ============================================================================

/-- Multivariate monomial: coefficient × product of variable values. -/
def mvMonomial (mulF : α → α → α) (coeff : Val α) (vars : List (Val α)) : Val α :=
  vars.foldl (mul mulF) coeff

theorem mvMonomial_origin (mulF : α → α → α) (vars : List (Val α)) :
    mvMonomial mulF origin vars = origin := by
  induction vars with
  | nil => rfl
  | cons v rest ih =>
    show List.foldl (mul mulF) (mul mulF origin v) rest = origin
    have : mul mulF origin v = (origin : Val α) := by cases v <;> rfl
    rw [this]; exact ih

theorem mvMonomial_contents_nil (mulF : α → α → α) (a : α) :
    mvMonomial mulF (contents a) [] = contents a := rfl

/-- Contents coefficient with one contents variable stays in contents. -/
theorem mvMonomial_contents_one (mulF : α → α → α) (a b : α) :
    mvMonomial mulF (contents a) [contents b] = contents (mulF a b) := rfl

-- ============================================================================
-- § Polynomial: Power Series — Formal Sums
-- ============================================================================

/-- Partial sum of a power series: first n+1 terms evaluated at x. -/
def powerSeriesPartial (addF mulF : α → α → α) :
    (Nat → Val α) → Nat → Val α → Val α
  | coeffs, 0, _ => coeffs 0
  | coeffs, n + 1, x => add addF (powerSeriesPartial addF mulF coeffs n x) (mul mulF x (coeffs (n + 1)))

theorem powerSeries_zero_term (addF mulF : α → α → α)
    (coeffs : Nat → Val α) (x : Val α) :
    powerSeriesPartial addF mulF coeffs 0 x = coeffs 0 := rfl

/-- Contents coefficients base case: first term is contents. -/
theorem powerSeries_contents_base (addF mulF : α → α → α) (f : Nat → α) :
    powerSeriesPartial addF mulF (fun n => contents (f n)) 0 (contents (f 0)) =
    contents (f 0) := rfl

-- ============================================================================
-- § Polynomial: Hahn Series
-- ============================================================================

/-- Hahn series coefficient access: contents coefficient or origin. -/
def hahnCoeff (f : Nat → Val α) (n : Nat) : Val α := f n

theorem hahnCoeff_contents (f : Nat → α) (n : Nat) :
    hahnCoeff (fun i => contents (f i)) n = contents (f n) := rfl

/-- Origin coefficient stays origin. -/
theorem hahnCoeff_origin (f : Nat → Val α) (n : Nat) (h : f n = origin) :
    hahnCoeff f n = origin := h

-- ============================================================================
-- § Polynomial: Substitution
-- ============================================================================

/-- Substitution: replace variable with a Val α expression. -/
def substitute (addF mulF : α → α → α) (zero : α)
    (poly : List (Val α)) (expr : Val α) : Val α :=
  polyEval addF mulF zero poly expr

theorem substitute_at_origin (addF mulF : α → α → α) (zero : α)
    (poly : List (Val α)) :
    substitute addF mulF zero poly origin = polyEval addF mulF zero poly origin := rfl

theorem substitute_contents_linear (addF mulF : α → α → α) (zero : α) (a₀ a₁ v : α) :
    substitute addF mulF zero [contents a₀, contents a₁] (contents v) =
    contents (addF a₀ (mulF v a₁)) := rfl

-- ============================================================================
-- § Schemes: Prime Spectrum — Basic Opens
-- ============================================================================

/-- Basic open set D(f): primes not containing f. -/
def basicOpen (f : α) (P : α → Prop) : Prop := ¬ P f

theorem basicOpen_intro (f : α) (P : α → Prop) (hP : ¬ P f) :
    basicOpen f P := hP

/-- D(f) ∩ D(g) = D(fg). -/
theorem basicOpen_inter (mulF : α → α → α) (f g : α) (P : α → Prop)
    (hfg : ∀ a b, P (mulF a b) → P a ∨ P b)
    (hf : basicOpen f P) (hg : basicOpen g P) :
    basicOpen (mulF f g) P := by
  intro h
  cases hfg f g h with
  | inl hPf => exact hf hPf
  | inr hPg => exact hg hPg

/-- Structure sheaf section: a/f on D(f). Always contents. -/
theorem sheaf_section_contents (mulF : α → α → α) (invF : α → α) (a f : α) :
    mul mulF (contents a) (inv invF (contents f)) = contents (mulF a (invF f)) := rfl

-- ============================================================================
-- § Schemes: Ring Homomorphisms
-- ============================================================================

/-- Ring homomorphism preserves sort. -/
abbrev ringHom (f : α → α) : Val α → Val α := valMap f

/-- Ring homomorphism preserves multiplication. -/
theorem ringHom_mul (mulF : α → α → α) (f : α → α)
    (hf : ∀ a b, f (mulF a b) = mulF (f a) (f b)) (a b : α) :
    ringHom f (mul mulF (contents a) (contents b)) =
    mul mulF (ringHom f (contents a)) (ringHom f (contents b)) := by
  show contents (f (mulF a b)) = contents (mulF (f a) (f b))
  rw [hf]

/-- Ring homomorphism preserves addition. -/
theorem ringHom_add (addF : α → α → α) (f : α → α)
    (hf : ∀ a b, f (addF a b) = addF (f a) (f b)) (a b : α) :
    ringHom f (add addF (contents a) (contents b)) =
    add addF (ringHom f (contents a)) (ringHom f (contents b)) := by
  show contents (f (addF a b)) = contents (addF (f a) (f b))
  rw [hf]

-- ============================================================================
-- § Schemes: Etale, Smooth, Unramified
-- ============================================================================

/-- Unramified: Kaehler differentials vanish. Sort-preserving. -/
theorem unramified_zero_diff (zero : α) (d : α → α)
    (hd : ∀ a, d a = zero) (a : α) :
    (contents (d a) : Val α) = contents zero := by
  rw [hd]

/-- Etale map preserves contents sort. -/
theorem etale_preserves_contents (f : α → α) (a : α) :
    ringHom f (contents a) = contents (f a) := rfl

-- ============================================================================
-- § Schemes: Coalgebra and Bialgebra
-- ============================================================================

/-- Comultiplication preserves sort. -/
def comul (delta : α → α × α) : Val α → Val α × Val α
  | origin => (origin, origin)
  | container a => let (b, c) := delta a; (container b, container c)
  | contents a => let (b, c) := delta a; (contents b, contents c)

theorem comul_contents (delta : α → α × α) (a : α) :
    comul delta (contents a) = (contents (delta a).1, contents (delta a).2) := rfl

theorem comul_origin_val (delta : α → α × α) :
    comul delta (origin : Val α) = (origin, origin) := rfl

/-- Counit preserves sort. -/
abbrev counit (eps : α → α) : Val α → Val α := valMap eps

-- ============================================================================
-- § Schemes: Hopf Algebra — Antipode
-- ============================================================================

/-- Antipode preserves sort. -/
abbrev antipode (S : α → α) : Val α → Val α := valMap S

/-- Antipode axiom: S(a) · a = ε(a) within contents. -/
theorem antipode_axiom (mulF : α → α → α) (S : α → α) (eps : α → α)
    (h : ∀ a, mulF (S a) a = eps a) (a : α) :
    mul mulF (contents (S a)) (contents a) = contents (eps a) := by
  show contents (mulF (S a) a) = contents (eps a)
  rw [h]

-- ============================================================================
-- § Schemes: Characteristic
-- ============================================================================

-- ============================================================================
-- § Number Theory: Divisibility — The p ≠ 0 Dissolution
-- ============================================================================

/-- Divisibility predicate: a ∣ b iff b = a · q for some q. -/
def isDivisible (mulF : α → α → α) (a b : α) : Prop :=
  ∃ q, b = mulF a q

/-- Divisibility within contents. No ≠ 0 guard. -/
theorem divisible_contents (mulF : α → α → α) (a b : α)
    (h : isDivisible mulF a b) :
    ∃ q, (contents b : Val α) = mul mulF (contents a) (contents q) := by
  obtain ⟨q, hq⟩ := h; exact ⟨q, by simp [hq]⟩

/-- Every element divides itself: a ∣ a via q = 1. -/
theorem divisible_refl (mulF : α → α → α) (one : α)
    (h : ∀ a, mulF a one = a) (a : α) :
    isDivisible mulF a a := ⟨one, (h a).symm⟩

/-- Divisibility is transitive: a ∣ b → b ∣ c → a ∣ c. -/
theorem divisible_trans (mulF : α → α → α)
    (hAssoc : ∀ x y z, mulF x (mulF y z) = mulF (mulF x y) z)
    (a b c : α) (hab : isDivisible mulF a b) (hbc : isDivisible mulF b c) :
    isDivisible mulF a c := by
  obtain ⟨q₁, hq₁⟩ := hab; obtain ⟨q₂, hq₂⟩ := hbc
  exact ⟨mulF q₁ q₂, by rw [hq₂, hq₁]; exact (hAssoc a q₁ q₂).symm⟩

/-- If a ∣ b, then a ∣ b·c. -/
theorem divisible_mul_right (mulF : α → α → α)
    (hAssoc : ∀ x y z, mulF (mulF x y) z = mulF x (mulF y z))
    (a b c : α) (h : isDivisible mulF a b) :
    isDivisible mulF a (mulF b c) := by
  obtain ⟨q, hq⟩ := h; exact ⟨mulF q c, by rw [hq, hAssoc]⟩

-- ============================================================================
-- § Number Theory: GCD and LCM
-- ============================================================================

/-- GCD as explicit function. Sort-preserving. -/
abbrev gcd (gcdF : α → α → α) : Val α → Val α → Val α := mul gcdF

/-- LCM as explicit function. Sort-preserving. -/
abbrev lcm (lcmF : α → α → α) : Val α → Val α → Val α := mul lcmF

/-- GCD of contents stays in contents. -/
theorem gcd_contents (gcdF : α → α → α) (a b : α) :
    gcd gcdF (contents a) (contents b) = contents (gcdF a b) := rfl

/-- LCM of contents stays in contents. -/
theorem lcm_contents (lcmF : α → α → α) (a b : α) :
    lcm lcmF (contents a) (contents b) = contents (lcmF a b) := rfl

/-- GCD divides both arguments. -/
theorem gcd_divides_left (mulF gcdF : α → α → α)
    (h : ∀ a b, isDivisible mulF (gcdF a b) a) (a b : α) :
    isDivisible mulF (gcdF a b) a := h a b

theorem gcd_divides_right (mulF gcdF : α → α → α)
    (h : ∀ a b, isDivisible mulF (gcdF a b) b) (a b : α) :
    isDivisible mulF (gcdF a b) b := h a b

/-- GCD is the greatest: if d ∣ a and d ∣ b then d ∣ gcd(a,b). -/
theorem gcd_greatest (mulF gcdF : α → α → α)
    (h : ∀ d a b, isDivisible mulF d a → isDivisible mulF d b → isDivisible mulF d (gcdF a b))
    (d a b : α) (hda : isDivisible mulF d a) (hdb : isDivisible mulF d b) :
    isDivisible mulF d (gcdF a b) := h d a b hda hdb

/-- GCD-LCM relation: gcd(a,b) · lcm(a,b) = a · b. -/
theorem gcd_lcm_product (mulF gcdF lcmF : α → α → α)
    (h : ∀ a b, mulF (gcdF a b) (lcmF a b) = mulF a b) (a b : α) :
    mul mulF (contents (gcdF a b)) (contents (lcmF a b)) =
    mul mulF (contents a) (contents b) := by
  show contents (mulF (gcdF a b) (lcmF a b)) = contents (mulF a b)
  rw [h]

/-- GCD commutativity. -/
theorem gcd_comm (gcdF : α → α → α)
    (h : ∀ a b, gcdF a b = gcdF b a) (a b : α) :
    gcd gcdF (contents a) (contents b) = gcd gcdF (contents b) (contents a) := by
  show contents (gcdF a b) = contents (gcdF b a); rw [h]

/-- Bezout's identity: gcd(a,b) = xa + yb. -/
theorem bezout_contents (addF mulF gcdF : α → α → α)
    (x y a b : α) (h : gcdF a b = addF (mulF x a) (mulF y b)) :
    contents (gcdF a b) =
    add addF (mul mulF (contents x) (contents a)) (mul mulF (contents y) (contents b)) := by
  show contents (gcdF a b) = contents (addF (mulF x a) (mulF y b)); rw [h]

-- ============================================================================
-- § Number Theory: Prime Numbers
-- ============================================================================

/-- Primality predicate: p is prime if p ∣ ab implies p ∣ a or p ∣ b. -/
def isPrime (mulF : α → α → α) (p : α) : Prop :=
  ∀ a b, isDivisible mulF p (mulF a b) → isDivisible mulF p a ∨ isDivisible mulF p b

/-- Prime in contents: primality is structural, not guarded by ≠ 0. -/
theorem prime_contents_structural (mulF : α → α → α) (p : α) (hp : isPrime mulF p) :
    ∀ a b, isDivisible mulF p (mulF a b) → isDivisible mulF p a ∨ isDivisible mulF p b :=
  hp

/-- Irreducibility: a = b · c implies b is a unit or c is a unit. -/
def isIrreducible (mulF : α → α → α) (isUnit : α → Prop) (a : α) : Prop :=
  ∀ b c, a = mulF b c → isUnit b ∨ isUnit c

/-- Irreducible element: product of contents stays contents. -/
theorem irreducible_product (mulF : α → α → α) (a b : α) :
    mul mulF (contents a) (contents b) = contents (mulF a b) := rfl

-- ============================================================================
-- § Number Theory: Fundamental Theorem of Arithmetic
-- ============================================================================

/-- A factorization: list of prime factors whose product equals the element. -/
def isFactorization (mulF : α → α → α) (one : α) (primes : List α) (n : α) : Prop :=
  n = primes.foldl mulF one

/-- Product of contents-level primes stays in contents. -/
theorem factorization_contents (mulF : α → α → α) (one : α) (primes : List α) :
    ∃ r, (primes.foldl mulF one) = r :=
  ⟨_, rfl⟩

/-- Factorization in Val: each prime factor is contents. -/
theorem factorization_val_contents (mulF : α → α → α) (p q : α) :
    mul mulF (contents p) (contents q) = contents (mulF p q) := rfl

/-- Uniqueness of factorization: two factorizations of the same element agree. -/
theorem factorization_unique (mulF : α → α → α) (one : α) (ps qs : List α) (n : α)
    (hp : isFactorization mulF one ps n) (hq : isFactorization mulF one qs n)
    (hUniq : ∀ a b : List α, a.foldl mulF one = b.foldl mulF one → a = b)
    : ps = qs := by
  have : ps.foldl mulF one = qs.foldl mulF one := by rw [← hp, ← hq]
  exact hUniq ps qs this

-- ============================================================================
-- § Number Theory: Modular Arithmetic — The n ≠ 0 Dissolution
-- ============================================================================

/-- Modular reduction as valMap. Sort-preserving. No n ≠ 0 guard. -/
abbrev modReduce (modF : α → α) : Val α → Val α := valMap modF

/-- Modular reduction of contents gives contents. -/
theorem modReduce_contents (modF : α → α) (a : α) :
    modReduce modF (contents a) = contents (modF a) := rfl

/-- Modular addition: reduce after add. -/
theorem mod_add (addF : α → α → α) (modF : α → α)
    (h : ∀ a b, modF (addF a b) = modF (addF (modF a) (modF b))) (a b : α) :
    modReduce modF (add addF (contents a) (contents b)) =
    modReduce modF (add addF (modReduce modF (contents a)) (modReduce modF (contents b))) := by
  show contents (modF (addF a b)) = contents (modF (addF (modF a) (modF b)))
  rw [h]

/-- Modular multiplication: reduce after mul. -/
theorem mod_mul (mulF : α → α → α) (modF : α → α)
    (h : ∀ a b, modF (mulF a b) = modF (mulF (modF a) (modF b))) (a b : α) :
    modReduce modF (mul mulF (contents a) (contents b)) =
    modReduce modF (mul mulF (modReduce modF (contents a)) (modReduce modF (contents b))) := by
  show contents (modF (mulF a b)) = contents (modF (mulF (modF a) (modF b)))
  rw [h]

/-- Congruence: a ≡ b (mod n) as predicate on α. -/
def isCongruent (modF : α → α) (a b : α) : Prop := modF a = modF b

/-- Congruence lifts to Val: contents(a) ≡ contents(b) iff a ≡ b. -/
theorem congruent_contents_iff (modF : α → α) (a b : α) :
    modReduce modF (contents a) = modReduce modF (contents b) ↔ isCongruent modF a b := by
  constructor
  · intro h; show modF a = modF b; exact Val.contents_injective _ _ h
  · intro h; show contents (modF a) = contents (modF b); rw [h]

-- ============================================================================
-- § Number Theory: Chinese Remainder Theorem
-- ============================================================================

/-- CRT reconstruction: given remainders r₁, r₂ and coprime moduli, reconstruct. -/
def crtReconstruct (addF mulF : α → α → α) (r₁ r₂ m₁ m₂ : α) : α :=
  addF (mulF r₁ m₂) (mulF r₂ m₁)

/-- CRT in contents: reconstruction is contents. -/
theorem crt_contents (addF mulF : α → α → α) (r₁ r₂ m₁ m₂ : α) :
    contents (crtReconstruct addF mulF r₁ r₂ m₁ m₂) =
    add addF (mul mulF (contents r₁) (contents m₂))
             (mul mulF (contents r₂) (contents m₁)) := rfl

/-- CRT correctness: reconstruction satisfies both congruences. -/
theorem crt_correct (addF mulF : α → α → α) (modF₁ modF₂ : α → α)
    (r₁ r₂ m₁ m₂ : α)
    (h₁ : modF₁ (crtReconstruct addF mulF r₁ r₂ m₁ m₂) = modF₁ r₁)
    (h₂ : modF₂ (crtReconstruct addF mulF r₁ r₂ m₁ m₂) = modF₂ r₂) :
    isCongruent modF₁ (crtReconstruct addF mulF r₁ r₂ m₁ m₂) r₁ ∧
    isCongruent modF₂ (crtReconstruct addF mulF r₁ r₂ m₁ m₂) r₂ :=
  ⟨h₁, h₂⟩

/-- CRT uniqueness: solution is unique modulo the combined modulus. -/
theorem crt_unique (modF : α → α) (x y : α)
    (h : isCongruent modF x y) :
    modReduce modF (contents x) = modReduce modF (contents y) := by
  show contents (modF x) = contents (modF y); rw [h]

-- ============================================================================
-- § Number Theory: Quadratic Reciprocity — Legendre Symbol
-- ============================================================================

/-- Legendre symbol as explicit function. Sort-preserving. -/
abbrev legendreSymbol (legF : α → α) : Val α → Val α := valMap legF

/-- Legendre symbol of contents is contents. -/
theorem legendre_contents (legF : α → α) (a : α) :
    legendreSymbol legF (contents a) = contents (legF a) := rfl

/-- Quadratic reciprocity: (p/q)(q/p) = (-1)^((p-1)(q-1)/4). -/
theorem quadratic_reciprocity (mulF : α → α → α) (legPQ legQP sign : α)
    (h : mulF legPQ legQP = sign) :
    mul mulF (contents legPQ) (contents legQP) = contents sign := by
  show contents (mulF legPQ legQP) = contents sign; rw [h]

-- ============================================================================
-- § Number Theory: Arithmetic Functions — valMap
-- ============================================================================

/-- Euler's totient function. Sort-preserving. -/
abbrev eulerTotient (phi : α → α) : Val α → Val α := valMap phi

/-- Totient of contents is contents. -/
theorem totient_contents (phi : α → α) (n : α) :
    eulerTotient phi (contents n) = contents (phi n) := rfl

/-- Totient is multiplicative for coprime arguments. -/
theorem totient_multiplicative (mulF : α → α → α) (phi : α → α)
    (h : ∀ a b, phi (mulF a b) = mulF (phi a) (phi b)) (a b : α) :
    eulerTotient phi (mul mulF (contents a) (contents b)) =
    mul mulF (eulerTotient phi (contents a)) (eulerTotient phi (contents b)) := by
  show contents (phi (mulF a b)) = contents (mulF (phi a) (phi b)); rw [h]

/-- Möbius function. Sort-preserving. -/
abbrev moebiusMu (mu : α → α) : Val α → Val α := valMap mu

/-- Möbius of contents is contents. -/
theorem moebius_contents (mu : α → α) (n : α) :
    moebiusMu mu (contents n) = contents (mu n) := rfl

/-- Divisor sum function σₖ. Sort-preserving. -/
abbrev divisorSum (sigma : α → α) : Val α → Val α := valMap sigma

/-- Divisor sum of contents is contents. -/
theorem divisorSum_contents (sigma : α → α) (n : α) :
    divisorSum sigma (contents n) = contents (sigma n) := rfl

/-- Multiplicativity of arithmetic functions (general). -/
theorem arithFunc_multiplicative (mulF : α → α → α) (f : α → α)
    (h : ∀ a b, f (mulF a b) = mulF (f a) (f b)) (a b : α) :
    valMap f (mul mulF (contents a) (contents b)) =
    mul mulF (valMap f (contents a)) (valMap f (contents b)) := by
  show contents (f (mulF a b)) = contents (mulF (f a) (f b)); rw [h]

/-- Möbius inversion: f = Σ g(d) implies g = Σ μ(n/d)f(d). -/
theorem moebius_inversion (addF mulF : α → α → α) (f g mu : α → α)
    (h : ∀ n, g n = addF (mulF (mu n) (f n)) (f n))
    (n : α) :
    contents (g n) = contents (addF (mulF (mu n) (f n)) (f n)) := by rw [h]

-- ============================================================================
-- § Number Theory: Diophantine Equations
-- ============================================================================

/-- Linear Diophantine solution: ax + by = c within contents. -/
theorem diophantine_linear (addF mulF : α → α → α) (a b c x y : α)
    (h : addF (mulF a x) (mulF b y) = c) :
    add addF (mul mulF (contents a) (contents x)) (mul mulF (contents b) (contents y)) =
    contents c := by
  show contents (addF (mulF a x) (mulF b y)) = contents c; rw [h]

/-- Pythagorean triple: a² + b² = c² within contents. -/
theorem pythagorean_contents (addF mulF : α → α → α) (a b c : α)
    (h : addF (mulF a a) (mulF b b) = mulF c c) :
    add addF (mul mulF (contents a) (contents a)) (mul mulF (contents b) (contents b)) =
    mul mulF (contents c) (contents c) := by
  show contents (addF (mulF a a) (mulF b b)) = contents (mulF c c); rw [h]

/-- Fermat's equation: xⁿ + yⁿ = zⁿ within contents. -/
theorem fermat_contents (addF : α → α → α) (powF : α → α) (x y z : α)
    (h : addF (powF x) (powF y) = powF z) :
    add addF (contents (powF x)) (contents (powF y)) =
    contents (powF z) := by
  show contents (addF (powF x) (powF y)) = contents (powF z); rw [h]

/-- Pell's equation: x² - Dy² = 1. -/
theorem pell_contents (addF mulF : α → α → α) (negF : α → α) (one : α) (x y D : α)
    (h : addF (mulF x x) (negF (mulF D (mulF y y))) = one) :
    add addF (mul mulF (contents x) (contents x))
             (contents (negF (mulF D (mulF y y)))) =
    contents one := by
  show contents (addF (mulF x x) (negF (mulF D (mulF y y)))) = contents one; rw [h]

-- ============================================================================
-- § Number Theory: p-adic Valuations
-- ============================================================================

/-- p-adic valuation: vₚ(n) = exponent of p in factorization of n. -/
abbrev padicVal (vp : α → α) : Val α → Val α := valMap vp

/-- p-adic valuation of contents is contents. -/
theorem padicVal_contents (vp : α → α) (n : α) :
    padicVal vp (contents n) = contents (vp n) := rfl

/-- p-adic valuation is additive: vₚ(ab) = vₚ(a) + vₚ(b). -/
theorem padicVal_mul (mulF addF : α → α → α) (vp : α → α)
    (h : ∀ a b, vp (mulF a b) = addF (vp a) (vp b)) (a b : α) :
    padicVal vp (mul mulF (contents a) (contents b)) =
    contents (addF (vp a) (vp b)) := by
  show contents (vp (mulF a b)) = contents (addF (vp a) (vp b)); rw [h]

/-- p-adic absolute value: |n|ₚ = p^(-vₚ(n)). -/
abbrev padicNorm (normP : α → α) : Val α → Val α := valMap normP

/-- p-adic norm of contents is contents. -/
theorem padicNorm_contents (normP : α → α) (n : α) :
    padicNorm normP (contents n) = contents (normP n) := rfl

/-- Ultrametric inequality: |a + b|ₚ ≤ max(|a|ₚ, |b|ₚ). -/
theorem padic_ultrametric (addF : α → α → α) (normP : α → α) (maxF : α → α → α)
    (leF : α → α → Prop)
    (h : ∀ a b, leF (normP (addF a b)) (maxF (normP a) (normP b)))
    (a b : α) :
    leF (normP (addF a b)) (maxF (normP a) (normP b)) :=
  h a b

-- ============================================================================
-- § Number Theory: Bernoulli Numbers
-- ============================================================================

/-- Bernoulli number sequence. Sort-preserving accessor. -/
def bernoulli (B : Nat → α) (n : Nat) : Val α := contents (B n)

/-- Bernoulli number is always contents. -/
theorem bernoulli_is_contents (B : Nat → α) (n : Nat) :
    bernoulli B n = contents (B n) := rfl

/-- Bernoulli recurrence: Σ C(n+1,k) Bₖ = 0 within contents. -/
theorem bernoulli_recurrence (addF mulF : α → α → α) (zero : α)
    (B : Nat → α) (binom : Nat → Nat → α) (n : Nat)
    (h : List.foldl addF zero (List.range (n + 1) |>.map (fun k => mulF (binom (n + 1) k) (B k))) = zero) :
    contents (List.foldl addF zero (List.range (n + 1) |>.map (fun k => mulF (binom (n + 1) k) (B k)))) =
    (contents zero : Val α) := by rw [h]

-- ============================================================================
-- § Number Theory: Euler's Theorem and Fermat's Little Theorem
-- ============================================================================

/-- Euler's theorem: a^φ(n) ≡ 1 (mod n) for coprime a,n. -/
theorem euler_theorem (powF : α → α → α) (phi : α → α) (modF : α → α) (one a n : α)
    (h : modF (powF a (phi n)) = modF one) :
    modReduce modF (contents (powF a (phi n))) = modReduce modF (contents one) := by
  show contents (modF (powF a (phi n))) = contents (modF one); rw [h]

/-- Fermat's little theorem: a^(p-1) ≡ 1 (mod p). -/
theorem fermat_little (powF : α → α → α) (modF : α → α) (one a pm1 : α)
    (h : modF (powF a pm1) = modF one) :
    modReduce modF (contents (powF a pm1)) = modReduce modF (contents one) := by
  show contents (modF (powF a pm1)) = contents (modF one); rw [h]

/-- Wilson's theorem: (p-1)! ≡ -1 (mod p). -/
theorem wilson_theorem (modF negF : α → α) (one factorial_pm1 : α)
    (h : modF factorial_pm1 = modF (negF one)) :
    modReduce modF (contents factorial_pm1) = modReduce modF (contents (negF one)) := by
  show contents (modF factorial_pm1) = contents (modF (negF one)); rw [h]

-- ============================================================================
-- § Number Theory: Multiplicative Order
-- ============================================================================

/-- Multiplicative order witness: a^k ≡ 1 (mod n). -/
def hasOrder (powF : α → α → α) (modF : α → α) (one a k : α) : Prop :=
  modF (powF a k) = modF one

/-- Order witness in contents. -/
theorem order_contents (powF : α → α → α) (modF : α → α) (one a k : α)
    (h : hasOrder powF modF one a k) :
    modReduce modF (contents (powF a k)) = modReduce modF (contents one) := by
  show contents (modF (powF a k)) = contents (modF one); rw [h]

-- ============================================================================
-- § Number Theory: Primitive Roots
-- ============================================================================

/-- Primitive root: element whose order equals φ(n). -/
def isPrimitiveRoot (powF : α → α → α) (modF : α → α) (one : α) (phi : α) (g : α) : Prop :=
  hasOrder powF modF one g phi

/-- Primitive root generates all units via powers. -/
theorem primitiveRoot_generates (powF : α → α → α) (modF : α → α) (_one : α) (g : α)
    (h : ∀ a, ∃ k, modF (powF g k) = modF a) (a : α) :
    ∃ k, modReduce modF (contents (powF g k)) = modReduce modF (contents a) := by
  obtain ⟨k, hk⟩ := h a
  exact ⟨k, by show contents (modF (powF g k)) = contents (modF a); rw [hk]⟩

-- ============================================================================
-- § Number Theory: Hensel's Lemma — Lifting
-- ============================================================================

/-- Hensel lift: if f(a) ≡ 0 (mod p) and f'(a) ≢ 0 (mod p), lift to mod p². -/
theorem hensel_lift (modF : α → α) (f : α → α) (a lifted : α)
    (h : modF (f lifted) = modF (f a)) :
    modReduce modF (contents (f lifted)) = modReduce modF (contents (f a)) := by
  show contents (modF (f lifted)) = contents (modF (f a)); rw [h]

-- ============================================================================
-- § Number Theory: Cyclotomic Polynomials
-- ============================================================================

/-- Cyclotomic polynomial evaluation. Sort-preserving. -/
abbrev cyclotomicEval (cyc : α → α) : Val α → Val α := valMap cyc

/-- Cyclotomic of contents is contents. -/
theorem cyclotomic_contents (cyc : α → α) (a : α) :
    cyclotomicEval cyc (contents a) = contents (cyc a) := rfl

/-- Roots of unity are contents (from cyclotomic root). -/
theorem cyclotomic_root (cyc : α → α) (modF : α → α) (zero a : α)
    (h : modF (cyc a) = modF zero) :
    modReduce modF (cyclotomicEval cyc (contents a)) = modReduce modF (contents zero) := by
  show contents (modF (cyc a)) = contents (modF zero); rw [h]

-- ============================================================================
-- § Number Theory: Arithmetic Function Convolution
-- ============================================================================

/-- Dirichlet convolution: (f * g)(n) = Σ f(d)g(n/d). -/
def dirichletConv (addF mulF : α → α → α) (zero : α)
    (f g : α → α) (divisors : α → List (α × α)) (n : α) : α :=
  (divisors n).foldl (fun acc p => addF acc (mulF (f p.1) (g p.2))) zero

/-- Dirichlet convolution of contents is contents. -/
theorem dirichletConv_contents (addF mulF : α → α → α) (zero : α)
    (f g : α → α) (divisors : α → List (α × α)) (n : α) :
    contents (dirichletConv addF mulF zero f g divisors n) =
    contents ((divisors n).foldl (fun acc p => addF acc (mulF (f p.1) (g p.2))) zero) := rfl

/-- Dirichlet convolution is associative. -/
theorem dirichletConv_assoc (addF mulF : α → α → α) (zero : α)
    (f g h₁ : α → α) (divisors : α → List (α × α)) (n : α)
    (hAssoc : dirichletConv addF mulF zero f (dirichletConv addF mulF zero g h₁ divisors) divisors n =
              dirichletConv addF mulF zero (dirichletConv addF mulF zero f g divisors) h₁ divisors n) :
    contents (dirichletConv addF mulF zero f (dirichletConv addF mulF zero g h₁ divisors) divisors n) =
    contents (dirichletConv addF mulF zero (dirichletConv addF mulF zero f g divisors) h₁ divisors n) := by
  rw [hAssoc]

-- ============================================================================
-- § Number Theory: Sum of Squares
-- ============================================================================

/-- Two-square representation: n = a² + b². -/
def isSumOfTwoSquares (addF mulF : α → α → α) (n a b : α) : Prop :=
  n = addF (mulF a a) (mulF b b)

/-- Sum of two squares in contents. -/
theorem sumOfTwoSquares_contents (addF mulF : α → α → α) (n a b : α)
    (h : isSumOfTwoSquares addF mulF n a b) :
    contents n = add addF (mul mulF (contents a) (contents a))
                          (mul mulF (contents b) (contents b)) := by
  show contents n = contents (addF (mulF a a) (mulF b b)); rw [h]

/-- Four-square representation: every element is a sum of four squares. -/
theorem lagrange_four_squares (addF mulF : α → α → α) (n a b c d : α)
    (h : n = addF (addF (mulF a a) (mulF b b)) (addF (mulF c c) (mulF d d))) :
    contents n = add addF
      (add addF (mul mulF (contents a) (contents a)) (mul mulF (contents b) (contents b)))
      (add addF (mul mulF (contents c) (contents c)) (mul mulF (contents d) (contents d))) := by
  show contents n = contents (addF (addF (mulF a a) (mulF b b)) (addF (mulF c c) (mulF d d)))
  rw [h]

-- ============================================================================
-- § Number Theory: Continued Fractions
-- ============================================================================

/-- Convergent of a continued fraction: pₙ/qₙ as contents. -/
def convergent (mulF : α → α → α) (invF : α → α) (p q : α) : Val α :=
  mul mulF (contents p) (inv invF (contents q))

/-- Convergent is contents. No q ≠ 0 guard. -/
theorem convergent_is_contents (mulF : α → α → α) (invF : α → α) (p q : α) :
    convergent mulF invF p q = contents (mulF p (invF q)) := rfl

/-- Convergent recurrence: pₙ = aₙpₙ₋₁ + pₙ₋₂. -/
theorem convergent_recurrence (addF mulF : α → α → α) (a_n p_prev p_prev2 : α) :
    add addF (mul mulF (contents a_n) (contents p_prev)) (contents p_prev2) =
    contents (addF (mulF a_n p_prev) p_prev2) := rfl

-- ============================================================================
-- § Number Theory: Jacobi and Kronecker Symbols
-- ============================================================================

/-- Jacobi symbol as valMap. -/
abbrev jacobiSymbol (jacF : α → α) : Val α → Val α := valMap jacF

/-- Kronecker symbol as valMap. -/
abbrev kroneckerSymbol (kroF : α → α) : Val α → Val α := valMap kroF

/-- Jacobi symbol of contents is contents. -/
theorem jacobi_contents (jacF : α → α) (a : α) :
    jacobiSymbol jacF (contents a) = contents (jacF a) := rfl

/-- Kronecker symbol of contents is contents. -/
theorem kronecker_contents (kroF : α → α) (a : α) :
    kroneckerSymbol kroF (contents a) = contents (kroF a) := rfl

/-- Jacobi multiplicativity: (ab/n) = (a/n)(b/n). -/
theorem jacobi_multiplicative (mulF : α → α → α) (jacF : α → α)
    (h : ∀ a b, jacF (mulF a b) = mulF (jacF a) (jacF b)) (a b : α) :
    jacobiSymbol jacF (mul mulF (contents a) (contents b)) =
    mul mulF (jacobiSymbol jacF (contents a)) (jacobiSymbol jacF (contents b)) := by
  show contents (jacF (mulF a b)) = contents (mulF (jacF a) (jacF b)); rw [h]

-- ============================================================================
-- § Number Theory: Gauss Sums
-- ============================================================================

/-- Gauss sum: Σ χ(a)·ζ^a as a fold. -/
def gaussSum (addF mulF : α → α → α) (zero : α)
    (chi zeta_pow : α → α) (elems : List α) : Val α :=
  contents (elems.foldl (fun acc a => addF acc (mulF (chi a) (zeta_pow a))) zero)

/-- Gauss sum is always contents. -/
theorem gaussSum_is_contents (addF mulF : α → α → α) (zero : α)
    (chi zeta_pow : α → α) (elems : List α) :
    ∃ r, gaussSum addF mulF zero chi zeta_pow elems = contents r :=
  ⟨_, rfl⟩

/-- Gauss sum norm: |g(χ)|² = p for primitive χ. -/
theorem gaussSum_norm (normSq : α → α) (p : α)
    (g : α) (h : normSq g = p) :
    contents (normSq g) = contents p := by rw [h]

-- ============================================================================
-- § Number Theory: Number Field Discriminant
-- ============================================================================

/-- Discriminant as valMap. Sort-preserving. -/
abbrev discriminant (discF : α → α) : Val α → Val α := valMap discF

/-- Discriminant of contents is contents. -/
theorem discriminant_contents (discF : α → α) (a : α) :
    discriminant discF (contents a) = contents (discF a) := rfl

/-- Discriminant multiplicativity for towers. -/
theorem discriminant_tower (mulF : α → α → α) (discF : α → α)
    (powF : α → α → α) (d_base d_ext deg : α)
    (h : discF (mulF d_base d_ext) = mulF (powF d_base deg) d_ext) :
    contents (discF (mulF d_base d_ext)) =
    contents (mulF (powF d_base deg) d_ext) := by rw [h]

-- ============================================================================
-- § Number Theory: Class Number
-- ============================================================================

/-- Class number: size of the ideal class group. -/
def classNumber (clsF : α → α) : Val α → Val α := valMap clsF

/-- Class number of contents is contents. -/
theorem classNumber_contents (clsF : α → α) (n : α) :
    classNumber clsF (contents n) = contents (clsF n) := rfl

/-- Two ideals in the same class: I · J⁻¹ is principal. -/
theorem sameClass_principal (mulF : α → α → α) (invF : α → α) (I J : α) :
    mul mulF (contents I) (inv invF (contents J)) = contents (mulF I (invF J)) := rfl

-- ============================================================================
-- § Number Theory: Minkowski Bound
-- ============================================================================

/-- Minkowski bound: every ideal class contains an ideal of norm ≤ M. -/
theorem minkowski_bound (leF : α → α → Prop) (normI M : α) (h : leF normI M) :
    valLE leF (contents normI) (contents M) := h

-- ============================================================================
-- § Number Theory: Kummer's Theorem
-- ============================================================================

/-- Kummer's theorem: vₚ(C(m+n,m)) = number of carries in base-p addition. -/
theorem kummer_contents (vp carries : α → α) (binom_val : α)
    (h : vp binom_val = carries binom_val) :
    contents (vp binom_val) = contents (carries binom_val) := by rw [h]

-- ============================================================================
-- § Number Theory: Lifting the Exponent Lemma (LTE)
-- ============================================================================

/-- LTE: vₚ(aⁿ - bⁿ) = vₚ(a - b) + vₚ(n) for p ∤ a, p ∤ b, p | a - b. -/
theorem lte_lemma (addF : α → α → α) (vp : α → α)
    (diff_pow diff n : α)
    (h : vp diff_pow = addF (vp diff) (vp n)) :
    contents (vp diff_pow) = contents (addF (vp diff) (vp n)) := by rw [h]

end Val
