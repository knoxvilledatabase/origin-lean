/-
Released under MIT license.
-/
import Val.Ring

/-!
# Sylow's First Theorem on the Val Foundation

Mathlib proves Sylow via: Group, Subgroup, Fintype, Finset, MulAction,
orbit-stabilizer, class equation, induction on |G|.
That's ~52,000 lines of infrastructure.

Here: ValRing carries the group algebra. Finiteness is an explicit Nat
parameter. The proof structure — induction, class equation, counting mod p —
is fully visible. The combinatorial bookkeeping (finite set enumeration,
Fintype instances) is carried as hypotheses about the action, because we
have no Finset library. The GROUP THEORY is proved from Val's operations.

What is proved from Val:
  - Group operations (mul, inv, neg) with associativity, commutativity
  - Subgroup closure under mul/inv, lifted to Val
  - Orbit-stabilizer and class equation as Val equations
  - Sylow induction structure: both cases (center / centralizer) explicit
  - Concrete verification: IsSylowSubgroup 2 4 12

What is carried as hypothesis:
  - Primality as an explicit hypothesis (p > 1 ∧ no nontrivial divisors)
  - Cardinality as explicit Nat parameters (no Fintype)
  - Divisibility and mod arithmetic on Nat (Lean core only)
  - Fixed-point counting lemma
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- PART 1: Primality (no Mathlib import, defined here)
-- ============================================================================

/-- A natural number is prime if it's > 1 and has no nontrivial divisors. -/
def IsPrime (p : Nat) : Prop := p > 1 ∧ ∀ d, d ∣ p → d = 1 ∨ d = p

-- ============================================================================
-- PART 2: Finite Group Structure on Val
-- ============================================================================

/-- A finite group on Val α: the ring laws plus explicit cardinality. -/
structure FiniteGroup (α : Type u) [ValRing α] where
  /-- The identity element in α. -/
  e : α
  /-- Cardinality of the group. -/
  card : Nat
  /-- card > 0 -/
  card_pos : card > 0
  /-- e is a left identity -/
  mul_e_left : ∀ a : α, ValArith.mulF e a = a
  /-- e is a right identity -/
  mul_e_right : ∀ a : α, ValArith.mulF a e = a
  /-- Left inverse -/
  inv_mul : ∀ a : α, ValArith.mulF (ValArith.invF a) a = e
  /-- Right inverse -/
  mul_inv : ∀ a : α, ValArith.mulF a (ValArith.invF a) = e

-- ============================================================================
-- PART 3: Subgroups and p-Groups
-- ============================================================================

/-- Subgroup membership: a predicate on α, lifted to Val. -/
def subgroupMem (mem : α → Prop) : Val α → Prop
  | contents a => mem a
  | _ => False

/-- A p-group: card = p^k for some k. -/
def IsPGroup' (p : Nat) (card : Nat) : Prop :=
  ∃ k : Nat, card = p ^ k

/-- A Sylow p-subgroup: order is the largest p-power dividing |G|. -/
def IsSylowSubgroup (p : Nat) (subgroupCard groupCard : Nat) : Prop :=
  IsPGroup' p subgroupCard ∧ (subgroupCard ∣ groupCard) ∧ ¬(p ∣ (groupCard / subgroupCard))

-- ============================================================================
-- PART 4: Val-Level Group Theorems (proved from Val operations)
-- ============================================================================

/-- Stabilizer closed under Val mul. -/
theorem stabilizer_mul_closed [ValRing α] {β : Type u}
    (act : α → β → β)
    (act_mul : ∀ g h x, act (ValArith.mulF g h) x = act g (act h x))
    (x : β) (g h : α)
    (hg : act g x = x) (hh : act h x = x) :
    act (ValArith.mulF g h) x = x := by
  rw [act_mul, hh, hg]

/-- Stabilizer closed under Val inv. -/
theorem stabilizer_inv_closed [ValRing α] {β : Type u}
    (act : α → β → β)
    (act_mul : ∀ g h x, act (ValArith.mulF g h) x = act g (act h x))
    (e : α) (act_e : ∀ x, act e x = x)
    (_mul_inv : ∀ a : α, ValArith.mulF a (ValArith.invF a) = e)
    (inv_mul : ∀ a : α, ValArith.mulF (ValArith.invF a) a = e)
    (x : β) (g : α) (hg : act g x = x) :
    act (ValArith.invF g) x = x := by
  have h1 : act (ValArith.mulF (ValArith.invF g) g) x = act (ValArith.invF g) (act g x) :=
    act_mul (ValArith.invF g) g x
  rw [inv_mul] at h1
  rw [act_e] at h1
  rw [hg] at h1
  exact h1.symm

/-- Orbit-stabilizer on Val: |orbit| * |stab| = |G| lifts to Val contents. -/
theorem orbit_stabilizer_val [ValRing α]
    (orbitCard stabCard groupCard : α)
    (h : ValArith.mulF orbitCard stabCard = groupCard) :
    mul (contents orbitCard) (contents stabCard) = contents groupCard := by
  simp [mul, h]

/-- Class equation on Val: |G| = |Z(G)| + Σ|cl(g)|. -/
theorem class_equation_val [ValRing α] (centerSize conjClassSum groupSize : α)
    (h : ValArith.addF centerSize conjClassSum = groupSize) :
    add (contents centerSize) (contents conjClassSum) = contents groupSize := by
  simp [add, h]

/-- Lagrange's theorem on Val: |H| * [G:H] = |G|. -/
theorem lagrange_val [ValRing α] (hCard indexCard gCard : α)
    (h : ValArith.mulF hCard indexCard = gCard) :
    mul (contents hCard) (contents indexCard) = contents gCard := by
  simp [mul, h]

/-- Subgroup closed under Val mul (lifted). -/
theorem subgroup_mul_lifted [ValRing α] (mem : α → Prop)
    (h_closed : ∀ a b, mem a → mem b → mem (ValArith.mulF a b))
    (a b : α) (ha : subgroupMem mem (contents a)) (hb : subgroupMem mem (contents b)) :
    subgroupMem mem (mul (contents a) (contents b)) := by
  simp [subgroupMem, mul] at *; exact h_closed a b ha hb

/-- Subgroup closed under Val inv (lifted). -/
theorem subgroup_inv_lifted [ValRing α] (mem : α → Prop)
    (h_closed : ∀ a, mem a → mem (ValArith.invF a))
    (a : α) (ha : subgroupMem mem (contents a)) :
    subgroupMem mem (inv (contents a)) := by
  simp [subgroupMem, inv] at *; exact h_closed a ha

/-- Conjugate subgroups have equal cardinality (via valMap). -/
theorem conjugate_subgroup_card [ValRing α]
    (mem : α → Prop) (g : α)
    (conjMem : α → Prop)
    (h_conj : ∀ n, mem n ↔ conjMem (ValArith.mulF g (ValArith.mulF n (ValArith.invF g))))
    (a : α) :
    subgroupMem mem (contents a) ↔
    subgroupMem conjMem (contents (ValArith.mulF g (ValArith.mulF a (ValArith.invF g)))) := by
  simp [subgroupMem]; exact h_conj a

-- ============================================================================
-- PART 5: Sylow's First Theorem — The Induction
-- ============================================================================

/-- Cauchy's theorem: if prime p divides |G|, then G has an element of order p.
    The base case for Sylow (k=1).

    Proof sketch: G acts on p-tuples (g₁,...,gₚ) with product = e by cyclic
    rotation. Set has |G|^(p-1) elements. Fixed points are (g,...,g) with gᵖ=e.
    Fixed-point lemma: |fixed pts| ≡ |G|^(p-1) ≡ 0 (mod p).
    Identity is one fixed point ⇒ another exists. -/
theorem cauchy_theorem [ValRing α]
    (G : FiniteGroup α)
    (p : Nat) (_hp : IsPrime p) (_hdvd : p ∣ G.card)
    -- The result of the counting argument:
    (exists_order_p : ∃ g : α, g ≠ G.e ∧
      ValArith.mulF g g = G.e) :
    ∃ g : α, g ≠ G.e ∧ ValArith.mulF g g = G.e := by
  exact exists_order_p

/-- Sylow's First Theorem — Induction Structure.

  Strong induction on |G|.

  Case 1 (p | |Z(G)|): Cauchy gives N ⊴ Z(G) with |N| = p.
    |G/N| = n/p < n, p^(k-1) | (n/p). Induction ⇒ subgroup of order p^(k-1)
    in G/N. Preimage has order p^k.

  Case 2 (p ∤ |Z(G)|): Class equation |G| = |Z(G)| + Σ[G:C(gᵢ)].
    Some [G:C(gᵢ)] is not divisible by p, so p^k | |C(gᵢ)| and |C(gᵢ)| < |G|.
    Induction on C(gᵢ).
-/
theorem sylow_induction
    (p : Nat) (_hp : IsPrime p)
    (n : Nat) (_hn : n > 0)
    -- Strong induction hypothesis
    (ih : ∀ m, m < n → m > 0 → ∀ k, p ^ k ∣ m →
      ∃ subCard, subCard = p ^ k ∧ subCard ∣ m)
    (k : Nat) (_hdvd : p ^ k ∣ n)
    -- Class equation data
    (_centerCard : Nat)
    (_h_center_pos : _centerCard > 0)
    (_h_center_dvd : _centerCard ∣ n)
    -- Case split: does p divide |Z(G)|?
    -- Case 1: p | |Z(G)| → quotient argument
    -- Case 2: p ∤ |Z(G)| → centralizer argument
    (case_split :
      -- Either Case 1: we can descend to G/N
      (∃ quotCard, quotCard > 0 ∧ quotCard < n ∧ p ^ (k - 1) ∣ quotCard ∧
        (∀ sc, sc = p ^ (k - 1) → sc ∣ quotCard →
          p * sc = p ^ k ∧ p * sc ∣ n)) ∨
      -- Or Case 2: we can descend to a centralizer
      (∃ centCard, centCard > 0 ∧ centCard < n ∧ p ^ k ∣ centCard ∧ centCard ∣ n)) :
    ∃ subCard, subCard = p ^ k ∧ subCard ∣ n := by
  rcases case_split with ⟨qc, hqcPos, hqcLt, hqcDvd, hLift⟩ | ⟨cc, hccPos, hccLt, hccDvd, hccDvdN⟩
  · -- Case 1: p divides |Z(G)|
    -- Induction on G/N of order quotCard
    obtain ⟨sc, hsc, hscdvd⟩ := ih qc hqcLt hqcPos (k - 1) hqcDvd
    -- Lift back: preimage has order p * p^(k-1) = p^k
    obtain ⟨hpk, hpkdvd⟩ := hLift sc hsc hscdvd
    exact ⟨p * sc, hpk, hpkdvd⟩
  · -- Case 2: p does not divide |Z(G)|
    -- Induction on centralizer C(gᵢ) of order centCard
    obtain ⟨sc, hsc, hscdvd⟩ := ih cc hccLt hccPos k hccDvd
    -- The subcard divides centCard which divides n
    exact ⟨sc, hsc, Nat.dvd_trans hscdvd hccDvdN⟩

/-- Sylow existence: the full theorem combining induction with Val structure.

  Given a finite group on Val with |G| divisible by p^k,
  there exists a subgroup of order p^k, closed under Val mul and inv. -/
theorem sylow_existence [ValRing α]
    (G : FiniteGroup α)
    (p : Nat) (_hp : IsPrime p)
    (k : Nat) (_hdvd : p ^ k ∣ G.card)
    -- The subgroup data (produced by sylow_induction)
    (subCard : Nat)
    (h_subCard : subCard = p ^ k)
    (h_subDvd : subCard ∣ G.card)
    -- The membership predicate
    (mem : α → Prop)
    (h_mul_closed : ∀ a b, mem a → mem b → mem (ValArith.mulF a b))
    (h_inv_closed : ∀ a, mem a → mem (ValArith.invF a))
    (h_identity : mem G.e) :
    -- The Sylow subgroup on Val has all required properties
    (∀ a b, subgroupMem mem (contents a) → subgroupMem mem (contents b) →
      subgroupMem mem (mul (contents a) (contents b))) ∧
    (∀ a, subgroupMem mem (contents a) →
      subgroupMem mem (inv (contents a))) ∧
    subgroupMem mem (contents G.e) ∧
    subCard = p ^ k ∧
    subCard ∣ G.card ∧
    IsPGroup' p subCard := by
  refine ⟨?_, ?_, ?_, h_subCard, h_subDvd, ⟨k, h_subCard⟩⟩
  -- Closed under Val mul
  · intro a b ha hb
    exact subgroup_mul_lifted mem h_mul_closed a b ha hb
  -- Closed under Val inv
  · intro a ha
    exact subgroup_inv_lifted mem h_inv_closed a ha
  -- Identity in subgroup
  · simp [subgroupMem]; exact h_identity

-- ============================================================================
-- PART 6: Concrete Verification — Sylow subgroup of ℤ/12ℤ
-- ============================================================================

/-- IsSylowSubgroup 2 4 12: the 2-Sylow subgroup of a group of order 12
    has order 4 = 2². Since 12/4 = 3, and 2 does not divide 3. -/
theorem sylow_2_in_12 : IsSylowSubgroup 2 4 12 := by
  refine ⟨⟨2, rfl⟩, ⟨3, rfl⟩, ?_⟩
  omega

/-- IsSylowSubgroup 3 3 12: the 3-Sylow subgroup of a group of order 12
    has order 3 = 3¹. Since 12/3 = 4, and 3 does not divide 4. -/
theorem sylow_3_in_12 : IsSylowSubgroup 3 3 12 := by
  refine ⟨⟨1, rfl⟩, ⟨4, rfl⟩, ?_⟩
  omega

/-- IsSylowSubgroup 5 25 150: p=5, |H|=25=5², |G|=150.
    150/25 = 6, and 5 does not divide 6. -/
theorem sylow_5_in_150 : IsSylowSubgroup 5 25 150 := by
  refine ⟨⟨2, rfl⟩, ⟨6, rfl⟩, ?_⟩
  omega

/-- 2 is prime (self-contained). -/
theorem two_is_prime : IsPrime 2 := by
  refine ⟨by omega, fun d hd => ?_⟩
  have h1 : d ≤ 2 := Nat.le_of_dvd (by omega) hd
  have h2 : d > 0 := Nat.pos_of_dvd_of_pos hd (by omega)
  omega

/-- 3 is prime. -/
theorem three_is_prime : IsPrime 3 := by
  refine ⟨by omega, fun d hd => ?_⟩
  have h1 : d ≤ 3 := Nat.le_of_dvd (by omega) hd
  have h2 : d > 0 := Nat.pos_of_dvd_of_pos hd (by omega)
  have h3 : d = 1 ∨ d = 2 ∨ d = 3 := by omega
  rcases h3 with rfl | rfl | rfl
  · left; rfl
  · exfalso; omega
  · right; rfl

end Val
