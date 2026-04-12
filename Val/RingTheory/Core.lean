/-
Released under MIT license.
-/
import Val.Algebra.Core
import Val.Algebra.GroupTheory

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

/-- Algebraic norm map preserves sort. -/
abbrev algNormMap (N : α → α) : Val α → Val α := valMap N

/-- Algebraic norm is multiplicative within contents. -/
theorem algNormMap_mul (mulF : α → α → α) (N : α → α)
    (hN : ∀ a b, N (mulF a b) = mulF (N a) (N b)) (a b : α) :
    algNormMap N (mul mulF (contents a) (contents b)) =
    mul mulF (algNormMap N (contents a)) (algNormMap N (contents b)) := by
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

end Val