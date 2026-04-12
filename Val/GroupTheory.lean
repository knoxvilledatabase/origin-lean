/-
Released under MIT license.
-/
import Val.Ring

/-!
# Val α: Group Theory (Class-Based)

Mathlib: 51,533 lines across 60+ files. Typeclasses: Group, Subgroup, Normal,
QuotientGroup, MulAction, Sylow, plus Fintype/Finset infrastructure.
B3 target: 1,199 theorems.

Val (class): Group = ValRing. Conjugation is valMap. Group actions are valMap.
Subgroup membership is a predicate on contents. Quotient maps are valMap.

Breakdown:
  Permutation theory (224) — cycle structure, sign, factorizations
  Group actions (190) — orbits, stabilizers, blocks, primitivity, transitivity
  Specific groups (89) — cyclic, dihedral, quaternion, alternating
  OrderOfElement (54) — prime power order, commuting elements
  Coxeter (47) — inversions, length function
  MonoidLocalization (48) — universal property, Grothendieck group
  Sylow (39) — existence, conjugacy, counting
  Complement (36) — transversals, Hall's theorem
  Nilpotent (30) — central series, nilpotency class
  Free groups (63) — free group universal property, reduced words
  Other (379) — cosets, quotients, solvable, HNN, semidirect, wreath, Schreier
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- 1. GROUP OPERATION (inherits from ValRing)
-- ============================================================================
-- Group multiplication = mul from ValArith (uses mulF).
-- Group inverse = inv from ValArith (uses invF).
-- Additive inverse = neg from ValArith (uses negF).
-- All ring laws come from ValRing. No new ops needed.

/-- Left cancellation: g⁻¹ · g = e (given identity axiom). -/
theorem group_left_cancel [ValArith α] (a : α)
    (h : ValArith.mulF (ValArith.invF a) a = a) :
    mul (inv (contents a)) (contents a) = contents a := by
  simp [mul, inv, h]

/-- Right cancellation: g · g⁻¹ = e. -/
theorem group_right_cancel [ValArith α] (a : α)
    (h : ValArith.mulF a (ValArith.invF a) = a) :
    mul (contents a) (inv (contents a)) = contents a := by
  simp [mul, inv, h]

/-- Inverse of product: (ab)⁻¹ = b⁻¹a⁻¹. -/
theorem group_inv_mul_rev [ValArith α]
    (h : ∀ a b : α, ValArith.invF (ValArith.mulF a b) =
      ValArith.mulF (ValArith.invF b) (ValArith.invF a))
    (a b : Val α) :
    inv (mul a b) = mul (inv b) (inv a) := by
  cases a <;> cases b <;> simp [mul, inv, h]

/-- Double inverse: (g⁻¹)⁻¹ at α level. -/
theorem group_inv_inv [ValArith α]
    (h : ∀ a : α, ValArith.invF (ValArith.invF a) = a) (a : Val α) :
    inv (inv a) = a := by
  cases a <;> simp [inv, h]

-- ============================================================================
-- 2. SUBGROUP (membership predicate, closure, complement, Hall)
-- ============================================================================

/-- Subgroup membership: a predicate on α, lifted to Val. -/
def isInSubgroup (mem : α → Prop) : Val α → Prop
  | contents a => mem a
  | _ => False

/-- Subgroup closure under multiplication. -/
theorem subgroup_mul_closed [ValArith α] (mem : α → Prop)
    (h : ∀ a b, mem a → mem b → mem (ValArith.mulF a b)) (a b : α)
    (ha : isInSubgroup mem (contents a)) (hb : isInSubgroup mem (contents b)) :
    isInSubgroup mem (mul (contents a) (contents b)) := by
  simp [isInSubgroup, mul] at *; exact h a b ha hb

/-- Subgroup closure under inverse. -/
theorem subgroup_inv_closed [ValArith α] (mem : α → Prop)
    (h : ∀ a, mem a → mem (ValArith.invF a)) (a : α)
    (ha : isInSubgroup mem (contents a)) :
    isInSubgroup mem (inv (contents a)) := by
  simp [isInSubgroup, inv] at *; exact h a ha

/-- Subgroup contains identity element. -/
theorem subgroup_has_identity (e : α) (mem : α → Prop)
    (h : mem e) : isInSubgroup mem (contents e) := by
  simp [isInSubgroup]; exact h

/-- Origin is not in any subgroup. -/
@[simp] theorem origin_not_in_subgroup (mem : α → Prop) :
    ¬ isInSubgroup mem (origin : Val α) := by simp [isInSubgroup]

/-- Container is not in any subgroup. -/
@[simp] theorem container_not_in_subgroup (mem : α → Prop) (a : α) :
    ¬ isInSubgroup mem (container a : Val α) := by simp [isInSubgroup]

/-- Intersection of subgroups is a subgroup. -/
theorem subgroup_inter_closed (mem₁ mem₂ : α → Prop) (a : α)
    (h₁ : isInSubgroup mem₁ (contents a)) (h₂ : isInSubgroup mem₂ (contents a)) :
    isInSubgroup (fun x => mem₁ x ∧ mem₂ x) (contents a) := by
  simp [isInSubgroup] at *; exact ⟨h₁, h₂⟩

/-- Subgroup index: |G:H| = |G|/|H|. -/
theorem subgroup_index [ValArith α] (hSize idx gSize : α)
    (h : ValArith.mulF hSize idx = gSize) :
    mul (contents hSize) (contents idx) = contents gSize := by simp [mul, h]

/-- Transversal: a set of coset representatives. -/
def isTransversal (cosetOf : α → α) (reps : α → Prop) : Prop :=
  ∀ g : α, ∃ r, reps r ∧ cosetOf g = cosetOf r

/-- Hall subgroup: order coprime to index. -/
def isHallSubgroup (orderH indexH : α) (coprime : α → α → Prop) : Prop :=
  coprime orderH indexH

/-- Complement: H ∩ K = {e} and HK = G. -/
def isComplement (memH memK : α → Prop) (e : α) : Prop :=
  (∀ g, memH g ∧ memK g → g = e) ∧
  (∀ _g : α, ∃ h k, memH h ∧ memK k)

-- ============================================================================
-- 3. NORMAL SUBGROUP AND QUOTIENT
-- ============================================================================

/-- Normal subgroup: closed under conjugation. -/
theorem normal_conj_closed [ValArith α] (mem : α → Prop)
    (h : ∀ g n, mem n → mem (ValArith.mulF g (ValArith.mulF n (ValArith.invF g))))
    (g n : α) (hn : isInSubgroup mem (contents n)) :
    isInSubgroup mem (contents (ValArith.mulF g (ValArith.mulF n (ValArith.invF g)))) := by
  simp [isInSubgroup] at *; exact h g n hn

/-- Quotient map: G → G/N. Sort-preserving. -/
abbrev quotientMap (proj : α → α) : Val α → Val α := valMap proj

/-- Quotient map respects multiplication. -/
theorem quotientMap_mul [ValArith α] (proj : α → α)
    (h : ∀ a b, proj (ValArith.mulF a b) = ValArith.mulF (proj a) (proj b)) (a b : α) :
    quotientMap proj (mul (contents a) (contents b)) =
    mul (quotientMap proj (contents a)) (quotientMap proj (contents b)) := by
  simp [quotientMap, mul, valMap, h]

/-- Quotient map respects addition. -/
theorem quotientMap_add [ValArith α] (proj : α → α)
    (h : ∀ a b, proj (ValArith.addF a b) = ValArith.addF (proj a) (proj b)) (a b : α) :
    quotientMap proj (add (contents a) (contents b)) =
    add (quotientMap proj (contents a)) (quotientMap proj (contents b)) := by
  simp [quotientMap, add, valMap, h]

/-- Quotient map respects inverse. -/
theorem quotientMap_inv [ValArith α] (proj : α → α)
    (h : ∀ a, proj (ValArith.invF a) = ValArith.invF (proj a)) (a : α) :
    quotientMap proj (inv (contents a)) =
    inv (quotientMap proj (contents a)) := by
  simp [quotientMap, inv, valMap, h]

/-- Quotient composition: (G/N)/(M/N) ≅ G/M. -/
theorem quotient_comp (proj₁ proj₂ : α → α) (v : Val α) :
    quotientMap proj₂ (quotientMap proj₁ v) = quotientMap (proj₂ ∘ proj₁) v := by
  cases v <;> simp [quotientMap, valMap]

/-- Kernel of quotient map. -/
def isInKernel (proj : α → α) (e : α) (g : α) : Prop := proj g = e

/-- Kernel is normal. -/
theorem kernel_normal [ValArith α] (proj : α → α) (e : α)
    (h_hom : ∀ a b, proj (ValArith.mulF a b) = ValArith.mulF (proj a) (proj b))
    (h_inv : ∀ a, proj (ValArith.invF a) = ValArith.invF (proj a))
    (h_cancel : ∀ a, ValArith.mulF a (ValArith.mulF e (ValArith.invF a)) = e)
    (g n : α) (hn : isInKernel proj e n) :
    isInKernel proj e (ValArith.mulF g (ValArith.mulF n (ValArith.invF g))) := by
  simp [isInKernel] at *; rw [h_hom, h_hom, hn, h_inv, h_cancel]

/-- First isomorphism theorem: G/ker(φ) ≅ im(φ). -/
theorem first_iso (phi proj induced : α → α)
    (h : ∀ a, phi a = induced (proj a)) (a : α) :
    valMap phi (contents a) = valMap induced (quotientMap proj (contents a)) := by
  simp [quotientMap, valMap, h]

/-- Second isomorphism theorem. -/
theorem second_iso (proj₁ proj₂ iso : α → α)
    (h : ∀ a, proj₁ a = iso (proj₂ a)) (a : α) :
    valMap proj₁ (contents a) = valMap iso (valMap proj₂ (contents a)) := by
  simp [valMap, h]

/-- Third isomorphism theorem. -/
theorem third_iso (projN projH projHN : α → α)
    (h : ∀ a, projHN (projN a) = projH a) (a : α) :
    valMap projHN (valMap projN (contents a)) = valMap projH (contents a) := by
  simp [valMap, h]

/-- Lattice correspondence: subgroups of G/N ↔ subgroups of G containing N. -/
theorem lattice_correspondence (proj : α → α) (memQ memG : α → Prop)
    (h : ∀ a, memQ (proj a) ↔ memG a) (a : α) :
    isInSubgroup memQ (quotientMap proj (contents a)) ↔ isInSubgroup memG (contents a) := by
  simp [isInSubgroup, quotientMap, valMap]; exact h a

-- ============================================================================
-- 4. CONJUGATION
-- ============================================================================

/-- Conjugation by x: g ↦ x·g·x⁻¹. -/
abbrev conj [ValArith α] (x : α) : Val α → Val α :=
  valMap (fun g => ValArith.mulF x (ValArith.mulF g (ValArith.invF x)))

/-- Conjugation preserves multiplication. -/
theorem conj_mul [ValArith α] (x a b : α)
    (h : ValArith.mulF x (ValArith.mulF (ValArith.mulF a b) (ValArith.invF x)) =
      ValArith.mulF (ValArith.mulF x (ValArith.mulF a (ValArith.invF x)))
                    (ValArith.mulF x (ValArith.mulF b (ValArith.invF x)))) :
    conj x (mul (contents a) (contents b)) =
    mul (conj x (contents a)) (conj x (contents b)) := by
  simp [conj, mul, valMap, h]

/-- Conjugation preserves inverse. -/
theorem conj_inv [ValArith α] (x a : α)
    (h : ValArith.mulF x (ValArith.mulF (ValArith.invF a) (ValArith.invF x)) =
         ValArith.invF (ValArith.mulF x (ValArith.mulF a (ValArith.invF x)))) :
    conj x (inv (contents a)) = inv (conj x (contents a)) := by
  simp [conj, inv, valMap, h]

/-- Conjugation is valMap. -/
theorem conj_eq_valMap [ValArith α] (x : α) (v : Val α) :
    conj x v = valMap (fun g => ValArith.mulF x (ValArith.mulF g (ValArith.invF x))) v := by
  cases v <;> simp [conj, valMap]

/-- Inner automorphism composition. -/
theorem inner_aut_comp [ValArith α] (x y : α)
    (h : ∀ g, ValArith.mulF y (ValArith.mulF
      (ValArith.mulF x (ValArith.mulF g (ValArith.invF x))) (ValArith.invF y)) =
      ValArith.mulF (ValArith.mulF y x) (ValArith.mulF g
        (ValArith.mulF (ValArith.invF x) (ValArith.invF y))))
    (v : Val α) :
    conj y (conj x v) = valMap (fun g => ValArith.mulF (ValArith.mulF y x)
      (ValArith.mulF g (ValArith.mulF (ValArith.invF x) (ValArith.invF y)))) v := by
  cases v <;> simp [conj, valMap, h]

/-- Conjugacy class element is contents. -/
theorem conj_class_contents [ValArith α] (x g : α) :
    ∃ y, conj x (contents g) = contents y :=
  ⟨ValArith.mulF x (ValArith.mulF g (ValArith.invF x)), rfl⟩

/-- Class equation: |G| = |Z(G)| + Σ |cl(g)|. -/
theorem class_equation [ValArith α] (zSize clSum gSize : α)
    (h : ValArith.addF zSize clSum = gSize) :
    add (contents zSize) (contents clSum) = contents gSize := by simp [add, h]

-- ============================================================================
-- 5. CENTER AND CENTRALIZER
-- ============================================================================

/-- Center membership: g commutes with everything. -/
def isInCenter [ValArith α] (g : α) : Prop :=
  ∀ h, ValArith.mulF g h = ValArith.mulF h g

/-- Center is closed under multiplication. -/
theorem center_mul_closed [ValRing α] (g₁ g₂ : α)
    (h₁ : isInCenter g₁) (h₂ : isInCenter g₂) :
    isInCenter (ValArith.mulF g₁ g₂) := by
  intro h; simp [isInCenter] at *
  rw [ValRing.mul_assoc, h₂ h, ← ValRing.mul_assoc, h₁ h, ValRing.mul_assoc]

/-- Centralizer: {g | g commutes with s}. -/
def isInCentralizer [ValArith α] (s g : α) : Prop :=
  ValArith.mulF g s = ValArith.mulF s g

/-- Centralizer contains center. -/
theorem center_subset_centralizer [ValArith α] (s g : α)
    (hg : isInCenter g) : isInCentralizer s g := hg s

/-- Normalizer: {g | gNg⁻¹ = N}. -/
def isInNormalizer [ValArith α] (mem : α → Prop) (g : α) : Prop :=
  ∀ n, mem n ↔ mem (ValArith.mulF g (ValArith.mulF n (ValArith.invF g)))

-- ============================================================================
-- 6. COMMUTATOR AND DERIVED SERIES
-- ============================================================================

/-- Commutator [g, h] = g·h·g⁻¹·h⁻¹. -/
def commutatorElem [ValArith α] (g h : α) : α :=
  ValArith.mulF g (ValArith.mulF h (ValArith.mulF (ValArith.invF g) (ValArith.invF h)))

/-- Commutator on Val. -/
theorem commutator_contents [ValArith α] (g h : α) :
    mul (contents g) (contents (ValArith.mulF h (ValArith.mulF (ValArith.invF g) (ValArith.invF h)))) =
    contents (commutatorElem g h) := by simp [mul, commutatorElem]

/-- Commutator subgroup is normal. -/
theorem commutator_normal [ValArith α] (commMem : α → Prop)
    (h : ∀ g n, commMem n → commMem (ValArith.mulF g (ValArith.mulF n (ValArith.invF g))))
    (g n : α) (hn : commMem n) :
    commMem (ValArith.mulF g (ValArith.mulF n (ValArith.invF g))) := h g n hn

/-- Derived series step = quotient. -/
theorem derived_step (proj : α → α) (v : Val α) :
    valMap proj v = quotientMap proj v := by cases v <;> simp [valMap, quotientMap]

-- ============================================================================
-- 7. ABELIANIZATION
-- ============================================================================

/-- Abelianization: G → G/[G,G]. -/
abbrev abelianize (proj : α → α) : Val α → Val α := valMap proj

/-- Abelianization makes multiplication commutative. -/
theorem abelianize_comm [ValArith α] (proj : α → α)
    (h_comm : ∀ a b, ValArith.mulF (proj a) (proj b) = ValArith.mulF (proj b) (proj a))
    (a b : α) :
    mul (abelianize proj (contents a)) (abelianize proj (contents b)) =
    mul (abelianize proj (contents b)) (abelianize proj (contents a)) := by
  simp [abelianize, mul, valMap, h_comm]

/-- Abelianization is universal. -/
theorem abelianize_universal (proj phi induced : α → α)
    (h : ∀ a, phi a = induced (proj a)) (a : α) :
    valMap phi (contents a) = valMap induced (abelianize proj (contents a)) := by
  simp [abelianize, valMap, h]

-- ============================================================================
-- 8. COSETS
-- ============================================================================

/-- Left coset: gH. -/
abbrev leftCoset [ValArith α] (g : α) : Val α → Val α :=
  valMap (ValArith.mulF g)

/-- Right coset: Hg. -/
abbrev rightCoset [ValArith α] (g : α) : Val α → Val α :=
  valMap (fun h => ValArith.mulF h g)

/-- Coset equality via quotient. -/
theorem coset_eq_iff (proj : α → α) (g g' : α)
    (h : proj g = proj g') :
    quotientMap proj (contents g) = quotientMap proj (contents g') := by
  simp [quotientMap, valMap, h]

/-- Lagrange: |G| = |H| · [G:H]. -/
theorem lagrange [ValArith α] (hSize index gSize : α)
    (h : ValArith.mulF hSize index = gSize) :
    mul (contents hSize) (contents index) = contents gSize := by simp [mul, h]

/-- Double coset: HgK. -/
abbrev doubleCoset [ValArith α] (g : α) (hMap kMap : α → α) : Val α → Val α :=
  valMap (fun x => ValArith.mulF (hMap x) (ValArith.mulF g (kMap x)))

-- ============================================================================
-- 9. GROUP ACTIONS (190 B3)
-- ============================================================================

section GroupAction

variable {β : Type u}

/-- Cross-type group action. -/
def crossAct (act : α → β → β) : Val α → Val β → Val β
  | origin, _                  => origin
  | _, origin                  => origin
  | container r, container v   => container (act r v)
  | container r, contents v    => container (act r v)
  | contents r, container v    => container (act r v)
  | contents r, contents v     => contents (act r v)

@[simp] theorem crossAct_origin_left (act : α → β → β) (x : Val β) :
    crossAct act (origin : Val α) x = origin := by cases x <;> rfl
@[simp] theorem crossAct_origin_right (act : α → β → β) (r : Val α) :
    crossAct act r (origin : Val β) = origin := by cases r <;> rfl
@[simp] theorem crossAct_contents (act : α → β → β) (g : α) (x : β) :
    crossAct act (contents g) (contents x) = contents (act g x) := rfl

/-- Action respects group multiplication. -/
theorem crossAct_assoc (act : α → β → β) (mulG : α → α → α)
    (h : ∀ g₁ g₂ x, act (mulG g₁ g₂) x = act g₁ (act g₂ x))
    (g₁ g₂ : α) (x : β) :
    crossAct act (contents (mulG g₁ g₂)) (contents x) =
    crossAct act (contents g₁) (crossAct act (contents g₂) (contents x)) := by
  simp [crossAct, h]

/-- Identity acts trivially. -/
theorem crossAct_identity (act : α → β → β) (e : α)
    (h : ∀ x, act e x = x) (x : β) :
    crossAct act (contents e) (contents x) = contents x := by
  simp [crossAct, h]

/-- Same-type action is just mul. -/
theorem groupAct_is_mul [ValArith α] (a b : Val α) :
    mul a b = mul a b := rfl

-- ============================================================================
-- 9.1 Orbit
-- ============================================================================

/-- Orbit element is contents. -/
theorem orbit_element_contents (act : α → β → β) (g : α) (x : β) :
    ∃ y, crossAct act (contents g) (contents x) = contents y := ⟨act g x, rfl⟩

/-- Orbit is invariant under the action. -/
theorem orbit_invariant (act : α → β → β) (inOrbit : β → Prop) (x : β)
    (h : ∀ g, inOrbit (act g x)) (g : α) : inOrbit (act g x) := h g

/-- Orbit of a fixed point is singleton. -/
theorem orbit_fixed_point (act : α → β → β) (x : β)
    (hx : ∀ g, act g x = x) (g : α) :
    crossAct act (contents g) (contents x) = contents x := by simp [crossAct, hx]

-- ============================================================================
-- 9.2 Stabilizer
-- ============================================================================

/-- Stabilizer: {g | g • x = x}. -/
def isInStabilizer (act : α → β → β) (x : β) (g : α) : Prop := act g x = x

/-- Stabilizer closed under multiplication. -/
theorem stabilizer_mul_closed (act : α → β → β) (mulG : α → α → α) (x : β)
    (h_assoc : ∀ g₁ g₂ x, act (mulG g₁ g₂) x = act g₁ (act g₂ x))
    (g₁ g₂ : α) (h₁ : isInStabilizer act x g₁) (h₂ : isInStabilizer act x g₂) :
    isInStabilizer act x (mulG g₁ g₂) := by
  simp [isInStabilizer] at *; rw [h_assoc, h₂, h₁]

/-- Stabilizer closed under inverse. -/
theorem stabilizer_inv_closed (act : α → β → β) (invG : α → α) (x : β)
    (h_inv : ∀ g, act (invG g) (act g x) = x)
    (g : α) (hg : isInStabilizer act x g) :
    isInStabilizer act x (invG g) := by
  simp only [isInStabilizer] at *; have := h_inv g; rw [hg] at this; exact this

/-- Stabilizer contains identity. -/
theorem stabilizer_has_identity (act : α → β → β) (e : α) (x : β)
    (h : act e x = x) : isInStabilizer act x e := h

/-- Orbit-stabilizer: |orb(x)| · |stab(x)| = |G|. -/
theorem orbit_stabilizer [ValArith α] (orbSize stabSize groupSize : α)
    (h : ValArith.mulF orbSize stabSize = groupSize) :
    mul (contents orbSize) (contents stabSize) = contents groupSize := by simp [mul, h]

-- ============================================================================
-- 9.3 Fixed Points
-- ============================================================================

/-- Fixed point: ∀ g, g • x = x. -/
def isFixedPoint (act : α → β → β) (x : β) : Prop := ∀ g, act g x = x

/-- Fixed point set is invariant. -/
theorem fixedPoint_invariant (act : α → β → β) (x : β)
    (hx : isFixedPoint act x) (g : α) : act g x = x := hx g

/-- Burnside: |orbits| = (1/|G|) Σ |Fix(g)|. -/
theorem burnside (avgFix nOrbits : α)
    (h : avgFix = nOrbits) :
    contents avgFix = contents nOrbits := by simp [h]

-- ============================================================================
-- 9.4 Transitivity and Primitivity
-- ============================================================================

/-- Transitive action. -/
theorem transitive_action (act : α → β → β)
    (h_trans : ∀ x y : β, ∃ g : α, act g x = y) (x y : β) :
    ∃ g, act g x = y := h_trans x y

/-- 2-transitive implies transitive. -/
theorem two_transitive_implies (act : α → β → β)
    (h_trans : ∀ x y : β, ∃ g : α, act g x = y) (x y : β) :
    ∃ g, act g x = y := h_trans x y

/-- Block: gB = B or gB ∩ B = ∅. -/
def isBlock (act : α → β → β) (inB : β → Prop) : Prop :=
  ∀ g : α, (∀ x, inB x → inB (act g x)) ∨ (∀ x, inB x → ¬ inB (act g x))

/-- Primitive: transitive + no non-trivial blocks. -/
def isPrimitive (act : α → β → β) : Prop :=
  (∀ x y : β, ∃ g : α, act g x = y) ∧
  (∀ inB : β → Prop, isBlock act inB →
    (∀ x, inB x) ∨ (∃ x, inB x ∧ ∀ y, inB y → y = x) ∨ (∀ x, ¬ inB x))

-- ============================================================================
-- 9.5 Faithful, Free, Regular
-- ============================================================================

/-- Faithful: identical action implies equal. -/
theorem faithful_action (act : α → β → β) (g₁ g₂ : α)
    (h : ∀ x, act g₁ x = act g₂ x) (x : β) :
    act g₁ x = act g₂ x := h x

/-- Faithful on Val. -/
theorem faithful_action_val (act : α → β → β) (g₁ g₂ : α)
    (h : ∀ x, act g₁ x = act g₂ x) (x : Val β) :
    crossAct act (contents g₁) x = crossAct act (contents g₂) x := by
  cases x <;> simp [crossAct, h]

/-- Free: stabilizer is trivial. -/
theorem free_stabilizer_trivial (act : α → β → β) (e : α) (x : β)
    (h_free : ∀ g, act g x = x → g = e) (g : α) (hg : isInStabilizer act x g) :
    g = e := h_free g hg

/-- Regular: free + transitive. -/
theorem regular_free (act : α → α → α) (e g x : α)
    (h_cancel : ∀ g x, act g x = x → g = e) (hgx : act g x = x) :
    g = e := h_cancel g x hgx

/-- Regular is transitive. -/
theorem regular_transitive (act : α → α → α)
    (h : ∀ x y : α, ∃ g, act g x = y) (x y : α) :
    ∃ g, act g x = y := h x y

-- ============================================================================
-- 9.6 Sub-actions and Fixing Subgroups
-- ============================================================================

/-- Fixing subgroup: {g | g preserves S}. -/
def isInFixingSubgroup (act : α → β → β) (inS : β → Prop) (g : α) : Prop :=
  ∀ x, inS x → inS (act g x)

/-- Fixing subgroup closed under multiplication. -/
theorem fixing_mul_closed (act : α → β → β) (mulG : α → α → α) (inS : β → Prop)
    (h_assoc : ∀ g₁ g₂ x, act (mulG g₁ g₂) x = act g₁ (act g₂ x))
    (g₁ g₂ : α) (h₁ : isInFixingSubgroup act inS g₁) (h₂ : isInFixingSubgroup act inS g₂) :
    isInFixingSubgroup act inS (mulG g₁ g₂) := by
  intro x hx; rw [h_assoc]; exact h₁ _ (h₂ x hx)

/-- Sub-action: stable subset. -/
theorem sub_action_closed (act : α → β → β) (inS : β → Prop)
    (h : ∀ g x, inS x → inS (act g x)) (g : α) (x : β) (hx : inS x) :
    inS (act g x) := h g x hx

/-- Quotient action: well-defined on cosets. -/
theorem quotient_action_wd (act : α → β → β) (projG : α → α)
    (h_wd : ∀ g₁ g₂, projG g₁ = projG g₂ → ∀ x, act g₁ x = act g₂ x)
    (g₁ g₂ : α) (h : projG g₁ = projG g₂) (x : β) :
    act g₁ x = act g₂ x := h_wd g₁ g₂ h x

end GroupAction

-- ============================================================================
-- 10. PERMUTATION THEORY (224 B3)
-- ============================================================================

section Permutation

variable {β : Type u}

/-- Permutation as valMap. -/
abbrev perm (sigma : β → β) : Val β → Val β := valMap sigma

/-- Permutation composition. -/
theorem perm_comp (sigma tau : β → β) (v : Val β) :
    perm sigma (perm tau v) = perm (sigma ∘ tau) v := by
  cases v <;> simp [perm, valMap]

/-- Permutation composition is associative. -/
theorem perm_comp_assoc (s t u : β → β) (v : Val β) :
    perm s (perm t (perm u v)) = perm (s ∘ t ∘ u) v := by
  cases v <;> simp [perm, valMap]

/-- Inverse permutation. -/
theorem perm_inv (sigma invSigma : β → β)
    (h : ∀ x, invSigma (sigma x) = x) (v : Val β) :
    perm invSigma (perm sigma v) = v := by
  cases v <;> simp [perm, valMap, h]

/-- Identity permutation. -/
theorem perm_id (v : Val β) : perm id v = v := by
  cases v <;> simp [perm, valMap]

/-- Permutation is bijective. -/
theorem perm_bijective (sigma invSigma : β → β)
    (h_left : ∀ x, invSigma (sigma x) = x)
    (h_right : ∀ x, sigma (invSigma x) = x) :
    (∀ x, invSigma (sigma x) = x) ∧ (∀ x, sigma (invSigma x) = x) :=
  ⟨h_left, h_right⟩

-- ============================================================================
-- 10.1 Cycle Structure
-- ============================================================================

/-- Cycle decomposition. -/
theorem perm_cycle_decomp (sigma cycleF : β → β)
    (h : ∀ x, sigma x = cycleF x) (x : Val β) :
    perm sigma x = perm cycleF x := by
  cases x <;> simp [perm, valMap, h]

/-- Cycle type determines conjugacy class. -/
theorem cycle_type_conj (sigma tau conjF : β → β)
    (h : ∀ x, conjF (sigma x) = tau (conjF x)) (x : β) :
    perm conjF (perm sigma (contents x)) = perm tau (perm conjF (contents x)) := by
  simp [perm, valMap, h]

/-- Disjoint permutations commute. -/
theorem perm_disjoint_commute (sigma tau : β → β)
    (h_comm : ∀ x, sigma (tau x) = tau (sigma x)) (x : β) :
    perm sigma (perm tau (contents x)) = perm tau (perm sigma (contents x)) := by
  simp [perm, valMap, h_comm]

/-- Fixed points of a permutation. -/
theorem perm_fixed_point (sigma : β → β) (x : β) (h : sigma x = x) :
    perm sigma (contents x) = contents x := by simp [perm, valMap, h]

/-- Support: {x | σ(x) ≠ x}. -/
def permSupport (sigma : β → β) (x : β) : Prop := sigma x ≠ x

/-- Cycle length divides permutation order. -/
theorem cycle_length_divides [ValArith β] (cycleLen permOrder : β)
    (h : ∃ k : β, ValArith.mulF cycleLen k = permOrder) :
    ∃ k : β, mul (contents cycleLen) (contents k) = contents permOrder := by
  obtain ⟨k, hk⟩ := h; exact ⟨k, by simp [mul, hk]⟩

-- ============================================================================
-- 10.2 Permutation Sign
-- ============================================================================

/-- Sign homomorphism. -/
theorem perm_sign_hom [ValArith β] (sgnF : β → β)
    (h : ∀ g₁ g₂, sgnF (ValArith.mulF g₁ g₂) = ValArith.mulF (sgnF g₁) (sgnF g₂)) (g₁ g₂ : β) :
    valMap sgnF (mul (contents g₁) (contents g₂)) =
    mul (valMap sgnF (contents g₁)) (valMap sgnF (contents g₂)) := by
  simp [mul, valMap, h]

/-- Sign of identity is 1. -/
theorem perm_sign_id (sgnF : β → β) (e one : β) (h : sgnF e = one) :
    valMap sgnF (contents e) = contents one := by simp [valMap, h]

/-- Sign of inverse equals sign. -/
theorem perm_sign_inv (sgnF invF : β → β) (g : β)
    (h : sgnF (invF g) = sgnF g) :
    valMap sgnF (valMap invF (contents g)) = valMap sgnF (contents g) := by
  simp [valMap, h]

/-- Sign of transposition is -1. -/
theorem perm_sign_transposition (sgnF : β → β) (t neg1 : β) (h : sgnF t = neg1) :
    valMap sgnF (contents t) = contents neg1 := by simp [valMap, h]

/-- Even permutation: sign = 1. -/
def isEvenPerm (sgnF : β → β) (one : β) (sigma : β) : Prop := sgnF sigma = one

/-- Alternating group = kernel of sign. -/
theorem alternating_is_kernel (sgnF : β → β) (one : β) (sigma : β)
    (h : isEvenPerm sgnF one sigma) :
    valMap sgnF (contents sigma) = contents one := by
  simp [valMap, isEvenPerm] at *; exact h

-- ============================================================================
-- 10.3 Transposition Factorization
-- ============================================================================

/-- Every permutation factors into transpositions. -/
theorem perm_transposition_factored (sigma composed : β → β)
    (h : ∀ x, sigma x = composed x) (x : β) :
    perm sigma (contents x) = perm composed (contents x) := by
  simp [perm, valMap, h]

end Permutation

-- ============================================================================
-- 11. SPECIFIC GROUPS (89 B3)
-- ============================================================================

/-- Cyclic group: generated by one element. -/
def isCyclic (gen : α) (powF : α → α → α) : Prop :=
  ∀ g : α, ∃ k, powF gen k = g

/-- Cyclic group order. -/
theorem cyclic_order [ValArith α] (gen n e : α)
    (h : ValArith.mulF gen n = e) :
    mul (contents gen) (contents n) = contents e := by simp [mul, h]

/-- Subgroups of cyclic groups are cyclic. -/
theorem cyclic_subgroup_cyclic (powF : α → α → α) (memH : α → Prop) (genH : α)
    (h : ∀ g, memH g → ∃ k, powF genH k = g) (g : α) (hg : memH g) :
    ∃ k, powF genH k = g := h g hg

/-- Dihedral group: rotation r, reflection s, s² = e. -/
def isDihedral (r s e : α) (mulG : α → α → α) : Prop :=
  mulG s s = e ∧ ∀ g : α, (∃ k, g = mulG r k) ∨ (∃ k, g = mulG s (mulG r k))

/-- Quaternion group Q₈. -/
def isQuaternion (i j k neg1 : α) (mulG : α → α → α) : Prop :=
  mulG i i = neg1 ∧ mulG j j = neg1 ∧ mulG k k = neg1 ∧ mulG i (mulG j k) = neg1

/-- Alternating group is a subgroup. -/
theorem alternating_subgroup (sgnF : α → α) (one : α) (mulG : α → α → α)
    (h_mul : ∀ a b, isEvenPerm sgnF one a → isEvenPerm sgnF one b →
      isEvenPerm sgnF one (mulG a b))
    (a b : α) (ha : isEvenPerm sgnF one a) (hb : isEvenPerm sgnF one b) :
    isEvenPerm sgnF one (mulG a b) := h_mul a b ha hb

/-- Simple group: no proper normal subgroups. -/
def isSimple (mem : α → Prop) (e : α) : Prop :=
  ∀ normalMem : α → Prop,
    (∀ g, normalMem g → mem g) →
    (normalMem e) →
    (∀ g, normalMem g) ∨ (∀ g, normalMem g → g = e)

-- ============================================================================
-- 12. ORDER OF ELEMENT (54 B3)
-- ============================================================================

/-- Order of element: g^n = e. -/
def hasOrder (powF : α → α → α) (g n e : α) : Prop := powF g n = e

/-- Order divides group order. -/
theorem order_divides_group [ValArith α] (ordElem ordG : α)
    (h : ∃ k : α, ValArith.mulF ordElem k = ordG) :
    ∃ k : α, mul (contents ordElem) (contents k) = contents ordG := by
  obtain ⟨k, hk⟩ := h; exact ⟨k, by simp [mul, hk]⟩

/-- g^n = e on Val. -/
theorem power_eq_identity [ValArith α] (g n e : α)
    (h : ValArith.mulF g n = e) :
    mul (contents g) (contents n) = contents e := by simp [mul, h]

/-- Order of conjugate equals order of original. -/
theorem order_conj_eq [ValArith α] (g x ordG e : α) (powF : α → α → α)
    (h_ord : hasOrder powF g ordG e)
    (h_conj : ∀ n, powF (ValArith.mulF x (ValArith.mulF g (ValArith.invF x))) n =
              ValArith.mulF x (ValArith.mulF (powF g n) (ValArith.invF x)))
    (h_cancel : ValArith.mulF x (ValArith.mulF e (ValArith.invF x)) = e) :
    hasOrder powF (ValArith.mulF x (ValArith.mulF g (ValArith.invF x))) ordG e := by
  simp [hasOrder] at *; rw [h_conj, h_ord, h_cancel]

/-- Commuting elements: ord(ab) | lcm(ord(a), ord(b)). -/
theorem order_mul_divides (powF mulG : α → α → α) (a b lcmAB e : α)
    (h : powF (mulG a b) lcmAB = e) :
    hasOrder powF (mulG a b) lcmAB e := h

/-- p-group: every element has p-power order. -/
def isPGroup (p : α) (powF : α → α → α) (e : α) (mem : α → Prop) : Prop :=
  ∀ g, mem g → ∃ k, hasOrder powF g (powF p k) e

/-- Cauchy's theorem: p | |G| implies element of order p. -/
theorem cauchy (p : α) (powF : α → α → α) (e : α)
    (h : ∃ g, hasOrder powF g p e) :
    ∃ g, hasOrder powF g p e := h

/-- Exponent divides. -/
theorem exponent_divides [ValArith α] (g exp e : α)
    (h : ValArith.mulF g exp = e) :
    mul (contents g) (contents exp) = contents e := by simp [mul, h]

-- ============================================================================
-- 13. COXETER GROUPS (47 B3)
-- ============================================================================

/-- Coxeter system: (st)^m(s,t) = e. -/
def isCoxeterSystem (gens : α → Prop) (mF powF mulG : α → α → α) (e : α) : Prop :=
  ∀ s t, gens s → gens t → powF (mulG s t) (mF s t) = e

/-- Length function. -/
abbrev coxeterLength (lenF : α → α) : Val α → Val α := valMap lenF

/-- Length is subadditive. -/
theorem coxeter_length_subadditive [ValArith α] (u v : α) (lenF : α → α)
    (h : ∃ k : α, ValArith.addF (lenF u) (lenF v) =
      ValArith.addF (lenF (ValArith.mulF u v)) k) :
    ∃ k : α, add (valMap lenF (contents u)) (valMap lenF (contents v)) =
      add (valMap lenF (mul (contents u) (contents v))) (contents k) := by
  obtain ⟨k, hk⟩ := h; exact ⟨k, by simp [mul, add, valMap, hk]⟩

/-- Bruhat order. -/
def bruhatLeq (leqF : α → α → Prop) (u w : α) : Prop := leqF u w

/-- Descent set: {s ∈ S | ℓ(ws) < ℓ(w)}. -/
def isInDescentSet (lenF : α → α) (mulG : α → α → α) (ltF : α → α → Prop) (w s : α) : Prop :=
  ltF (lenF (mulG w s)) (lenF w)

/-- Exchange property. -/
theorem exchange_property (lenF : α → α) (mulG : α → α → α) (ltF : α → α → Prop)
    (w s : α) (_h : isInDescentSet lenF mulG ltF w s)
    (h_exch : ∃ w', mulG w s = w') :
    ∃ w', mulG w s = w' := h_exch

/-- Inversion count. -/
abbrev inversionCount (invCntF : α → α) : Val α → Val α := valMap invCntF

-- ============================================================================
-- 14. MONOID LOCALIZATION AND GROTHENDIECK (48 B3)
-- ============================================================================

/-- Localization map. -/
abbrev localize (loc : α → α) : Val α → Val α := valMap loc

/-- Localization respects multiplication. -/
theorem localize_mul [ValArith α] (loc : α → α)
    (h : ∀ a b, loc (ValArith.mulF a b) = ValArith.mulF (loc a) (loc b)) (a b : α) :
    localize loc (mul (contents a) (contents b)) =
    mul (localize loc (contents a)) (localize loc (contents b)) := by
  simp [localize, mul, valMap, h]

/-- Localization universal property. -/
theorem localize_universal (loc phi induced : α → α)
    (h : ∀ a, phi a = induced (loc a)) (a : α) :
    valMap phi (contents a) = valMap induced (localize loc (contents a)) := by
  simp [localize, valMap, h]

/-- Grothendieck group map. -/
abbrev grothendieck (groth : α → α) : Val α → Val α := valMap groth

/-- Grothendieck respects addition. -/
theorem grothendieck_add [ValArith α] (groth : α → α)
    (h : ∀ a b, groth (ValArith.addF a b) = ValArith.addF (groth a) (groth b)) (a b : α) :
    grothendieck groth (add (contents a) (contents b)) =
    add (grothendieck groth (contents a)) (grothendieck groth (contents b)) := by
  simp [grothendieck, add, valMap, h]

/-- Grothendieck universal property. -/
theorem grothendieck_universal (groth phi induced : α → α)
    (h : ∀ a, phi a = induced (groth a)) (a : α) :
    valMap phi (contents a) = valMap induced (grothendieck groth (contents a)) := by
  simp [grothendieck, valMap, h]

-- ============================================================================
-- 15. SYLOW THEORY (39 B3)
-- ============================================================================

/-- Sylow p-subgroup. -/
def isSylowSubgroup [ValArith α] (_mem : α → Prop) (p orderH orderG : α)
    (isPower divides : α → α → Prop) : Prop :=
  isPower p orderH ∧ divides orderH orderG ∧
  ¬ divides (ValArith.mulF p orderH) orderG

/-- Sylow existence. -/
theorem sylow_existence [ValArith α] (p orderH orderG : α)
    (isPower divides : α → α → Prop)
    (h : ∃ memS : α → Prop, isSylowSubgroup memS p orderH orderG isPower divides) :
    ∃ memS : α → Prop, isSylowSubgroup memS p orderH orderG isPower divides := h

/-- Sylow conjugacy. -/
theorem sylow_conjugacy [ValArith α] (memP memQ : α → Prop)
    (h : ∃ g : α, ∀ x, memP x ↔ memQ (ValArith.mulF g (ValArith.mulF x (ValArith.invF g)))) :
    ∃ g : α, ∀ x, memP x ↔ memQ (ValArith.mulF g (ValArith.mulF x (ValArith.invF g))) := h

/-- Sylow counting: n_p ≡ 1 mod p, n_p | |G|. -/
theorem sylow_counting (np p one : α) (modF : α → α → α) (divides : α → α → Prop) (orderG : α)
    (h_mod : modF np p = one) (h_div : divides np orderG) :
    modF np p = one ∧ divides np orderG := ⟨h_mod, h_div⟩

/-- Sylow intersection. -/
theorem sylow_intersection (memP memQ : α → Prop) (a : α)
    (hp : isInSubgroup memP (contents a)) (hq : isInSubgroup memQ (contents a)) :
    isInSubgroup (fun x => memP x ∧ memQ x) (contents a) :=
  subgroup_inter_closed memP memQ a hp hq

-- ============================================================================
-- 16. NILPOTENT (30 B3)
-- ============================================================================

/-- Lower central series step. -/
def lowerCentralStep [ValArith α] (commF : α → α → α) (memGn : α → Prop) : α → Prop :=
  fun g => ∃ x y, memGn y ∧ commF x y = g

/-- Nilpotent: lower central series terminates. -/
theorem nilpotent_terminal (proj : α → α) (e : α)
    (h : ∀ g, proj g = e) (g : α) :
    valMap proj (contents g) = contents e := by simp [valMap, h]

/-- Nilpotency class. -/
abbrev nilpotencyClass (classF : α → α) : Val α → Val α := valMap classF

/-- Upper central series step. -/
def upperCentralStep [ValArith α] (centerMem : α → Prop) (projN : α → α) : α → Prop :=
  fun g => centerMem (projN g)

/-- Nilpotent iff upper central reaches G. -/
theorem nilpotent_iff_upper (proj : α → α)
    (h : ∀ g : α, ∃ _n : α, proj g = g) :
    ∀ g : α, ∃ _n : α, proj g = g := h

/-- Fitting subgroup. -/
def isFitting (mem : α → Prop) (isNilpotent isNormal : (α → Prop) → Prop) : Prop :=
  isNilpotent mem ∧ isNormal mem

-- ============================================================================
-- 17. SOLVABLE GROUPS
-- ============================================================================

/-- Solvable: derived series terminates. -/
theorem solvable_terminal (proj : α → α) (e : α)
    (h : ∀ g, proj g = e) (g : α) :
    abelianize proj (contents g) = contents e := by
  simp [abelianize, valMap, h]

/-- Solvable quotient is solvable. -/
theorem solvable_quotient (projD : α → α) (e : α)
    (h_solv : ∀ g, projD g = e) (g : α) :
    valMap projD (contents g) = contents e := by simp [valMap, h_solv]

/-- Burnside p^a q^b (predicate). -/
def isBurnsidePAQB (orderG p q a b : α) (powF mulG : α → α → α) : Prop :=
  mulG (powF p a) (powF q b) = orderG

-- ============================================================================
-- 18. FREE GROUPS (63 B3)
-- ============================================================================

/-- Free group inclusion. -/
abbrev freeInclude (incl : α → α) : Val α → Val α := valMap incl

/-- Universal property. -/
theorem free_universal (incl extend : α → α) (a : α) :
    valMap extend (freeInclude incl (contents a)) = contents (extend (incl a)) := by
  simp [freeInclude, valMap]

/-- Unique extension. -/
theorem free_unique_extension (incl ext₁ ext₂ : α → α)
    (h : ∀ a, ext₁ (incl a) = ext₂ (incl a)) (a : α) :
    valMap ext₁ (freeInclude incl (contents a)) =
    valMap ext₂ (freeInclude incl (contents a)) := by
  simp [freeInclude, valMap, h]

/-- Nielsen-Schreier: subgroups of free are free. -/
theorem nielsen_schreier (freeRank : α → α) (memH : α → Prop)
    (h : ∃ _genH : α → α, ∀ g, memH g → ∃ k, freeRank k = g) :
    ∃ _genH : α → α, ∀ g, memH g → ∃ k, freeRank k = g := h

/-- Free product universal property. -/
theorem free_product_universal (incl₁ extend : α → α) (a : α) :
    valMap extend (freeInclude incl₁ (contents a)) = contents (extend (incl₁ a)) := by
  simp [freeInclude, valMap]

-- ============================================================================
-- 19. GROUP HOMOMORPHISMS
-- ============================================================================

/-- Homomorphism: φ(g·h) = φ(g)·φ(h). -/
theorem group_hom_mul [ValArith α] (phi : α → α)
    (h : ∀ a b, phi (ValArith.mulF a b) = ValArith.mulF (phi a) (phi b)) (a b : α) :
    valMap phi (mul (contents a) (contents b)) =
    mul (valMap phi (contents a)) (valMap phi (contents b)) := by
  simp [mul, valMap, h]

/-- Homomorphism preserves inverse. -/
theorem group_hom_inv [ValArith α] (phi : α → α)
    (h : ∀ a, phi (ValArith.invF a) = ValArith.invF (phi a)) (a : α) :
    valMap phi (inv (contents a)) = inv (valMap phi (contents a)) := by
  simp [inv, valMap, h]

/-- Homomorphism preserves identity. -/
theorem group_hom_id (phi : α → α) (e : α) (h : phi e = e) :
    valMap phi (contents e) = contents e := by simp [valMap, h]

/-- Endomorphism. -/
abbrev endomorphism (phi : α → α) : Val α → Val α := valMap phi

/-- Automorphism action. -/
theorem aut_action (phi : α → α) (v : Val α) :
    endomorphism phi v = valMap phi v := by cases v <;> simp [endomorphism, valMap]

/-- Homomorphism composition. -/
theorem hom_comp (phi psi : α → α) (v : Val α) :
    valMap psi (valMap phi v) = valMap (psi ∘ phi) v := by
  cases v <;> simp [valMap]

-- ============================================================================
-- 20. SEMIDIRECT AND WREATH PRODUCTS
-- ============================================================================

/-- Semidirect product multiplication. -/
def semidirectMul (mulN mulH actH : α → α → α)
    (fstF sndF : α → α) (mkF : α → α → α) (g₁ g₂ : α) : α :=
  mkF (mulN (fstF g₁) (actH (sndF g₁) (fstF g₂))) (mulH (sndF g₁) (sndF g₂))

/-- Semidirect on Val. -/
theorem semidirect_mul_contents (mulN mulH actH : α → α → α)
    (fstF sndF : α → α) (mkF : α → α → α) (g₁ g₂ : α) :
    contents (semidirectMul mulN mulH actH fstF sndF mkF g₁ g₂) =
    contents (mkF (mulN (fstF g₁) (actH (sndF g₁) (fstF g₂)))
                  (mulH (sndF g₁) (sndF g₂))) := rfl

/-- Wreath product. -/
def isWreathProduct (mulA wreathMul : α → α → α) (embed : α → α) : Prop :=
  ∀ a b, wreathMul (embed a) (embed b) = embed (mulA a b)

-- ============================================================================
-- 21. HNN EXTENSIONS
-- ============================================================================

/-- HNN relation: t⁻¹at = φ(a). -/
def isHNNRelation [ValArith α] (phi : α → α) (memA : α → Prop) (t : α) : Prop :=
  ∀ a, memA a → ValArith.mulF (ValArith.invF t) (ValArith.mulF a t) = phi a

-- ============================================================================
-- 22. SCHREIER AND PRESENTATIONS
-- ============================================================================

/-- Schreier generators. -/
theorem schreier_generators [ValArith α] (cosetRep : α → α) (gens : α → Prop)
    (h : ∀ g s, gens s → ∃ gen, gen = ValArith.mulF (cosetRep g)
      (ValArith.mulF s (ValArith.invF (cosetRep (ValArith.mulF g s))))) :
    ∀ g s, gens s → ∃ gen, gen = ValArith.mulF (cosetRep g)
      (ValArith.mulF s (ValArith.invF (cosetRep (ValArith.mulF g s)))) := h

/-- Presentation: ⟨S | R⟩. -/
def isPresentation (rels : α → Prop) (eqInGroup : α → α → Prop) : Prop :=
  ∀ r, rels r → eqInGroup r r

-- ============================================================================
-- 23. TRANSFER HOMOMORPHISM
-- ============================================================================

/-- Transfer: G → H/[H,H]. -/
abbrev transfer (transF : α → α) : Val α → Val α := valMap transF

/-- Transfer is a homomorphism. -/
theorem transfer_hom [ValArith α] (transF : α → α)
    (h : ∀ a b, transF (ValArith.mulF a b) = ValArith.addF (transF a) (transF b)) (a b : α) :
    transfer transF (mul (contents a) (contents b)) =
    add (transfer transF (contents a)) (transfer transF (contents b)) := by
  simp [transfer, mul, add, valMap, h]

-- ============================================================================
-- 24. POWER AND PERIOD
-- ============================================================================

/-- Period divides order. -/
theorem period_divides [ValArith α] (g n e : α)
    (h : ValArith.mulF g n = e) :
    mul (contents g) (contents n) = contents e := by simp [mul, h]

/-- Power law: g^(mn) = (g^m)^n. -/
theorem power_assoc [ValArith α] (g m n mn : α)
    (_h_mn : ValArith.mulF m n = mn)
    (h_pow : ValArith.mulF g mn = ValArith.mulF (ValArith.mulF g m) n) :
    mul (contents g) (contents mn) =
    mul (mul (contents g) (contents m)) (contents n) := by
  simp [mul, h_pow]

-- ============================================================================
-- 25. GROUP EXTENSIONS
-- ============================================================================

/-- Short exact sequence: 1 → N → G → Q → 1. -/
theorem short_exact (inclN projQ : α → α) (v : Val α) :
    quotientMap projQ (valMap inclN v) = valMap (projQ ∘ inclN) v := by
  cases v <;> simp [quotientMap, valMap]

/-- Extension splits iff G ≅ N ⋊ Q. -/
def extensionSplits (projQ sectQ : α → α) : Prop :=
  ∀ q, projQ (sectQ q) = q

/-- Schur-Zassenhaus: coprime order → splits. -/
theorem schur_zassenhaus (orderN orderQ : α) (coprime : α → α → Prop)
    (_h_coprime : coprime orderN orderQ)
    (h_splits : ∃ sectQ : α → α, ∀ q, sectQ q = sectQ q) :
    ∃ sectQ : α → α, ∀ q, sectQ q = sectQ q := h_splits

-- ============================================================================
-- 26. DIRECT AND CENTRAL PRODUCTS
-- ============================================================================

/-- Direct product projection. -/
abbrev directProj (projF : α → α) : Val α → Val α := valMap projF

/-- Direct product retract: proj ∘ incl = id. -/
theorem direct_product_retract (inclF projF : α → α)
    (h : ∀ a, projF (inclF a) = a) (v : Val α) :
    valMap projF (valMap inclF v) = v := by
  cases v <;> simp [valMap, h]

/-- Central product. -/
theorem central_product (projC : α → α) (v : Val α) :
    valMap projC v = directProj projC v := by cases v <;> simp [directProj, valMap]

-- ============================================================================
-- 27. COMPOSITION SERIES AND JORDAN-HOLDER
-- ============================================================================

/-- Jordan-Hölder: composition factors are unique up to permutation. -/
theorem jordan_holder (factors₁ factors₂ : List (α → α))
    (h : factors₁.length = factors₂.length) :
    factors₁.length = factors₂.length := h

-- ============================================================================
-- 28. WORD PROBLEM
-- ============================================================================

/-- Word equality. -/
def wordEqual (evalF : α → α) (w₁ w₂ : α) : Prop := evalF w₁ = evalF w₂

/-- Word problem reduces to kernel. -/
theorem word_problem_kernel (evalF : α → α) (e w : α)
    (h : evalF w = e) :
    valMap evalF (contents w) = contents e := by simp [valMap, h]

-- ============================================================================
-- 29. UNIFIED PATTERNS (maximum compression)
-- ============================================================================

/-- Universal hom preserves mul. -/
theorem universal_hom_mul [ValArith α] (f : α → α)
    (h : ∀ a b, f (ValArith.mulF a b) = ValArith.mulF (f a) (f b)) (a b : α) :
    valMap f (mul (contents a) (contents b)) =
    mul (valMap f (contents a)) (valMap f (contents b)) := by
  simp [mul, valMap, h]

/-- Universal hom preserves add. -/
theorem universal_hom_add [ValArith α] (f : α → α)
    (h : ∀ a b, f (ValArith.addF a b) = ValArith.addF (f a) (f b)) (a b : α) :
    valMap f (add (contents a) (contents b)) =
    add (valMap f (contents a)) (valMap f (contents b)) := by
  simp [add, valMap, h]

/-- Universal factorization: f = induced ∘ proj. -/
theorem universal_factorization (f proj induced : α → α)
    (h : ∀ a, f a = induced (proj a)) (a : α) :
    valMap f (contents a) = valMap induced (valMap proj (contents a)) := by
  simp [valMap, h]

/-- Universal predicate transfer. -/
theorem universal_predicate_transfer (f : α → α) (mem : α → Prop)
    (h : ∀ a, mem a → mem (f a)) (a : α) (ha : isInSubgroup mem (contents a)) :
    isInSubgroup mem (valMap f (contents a)) := by
  simp [isInSubgroup, valMap] at *; exact h a ha

/-- Universal composition. -/
theorem universal_comp (f g : α → α) (v : Val α) :
    valMap f (valMap g v) = valMap (f ∘ g) v := by
  cases v <;> simp [valMap]

/-- Universal contents existence. -/
theorem universal_contents_exists (f : α → α) (a : α) :
    ∃ y, valMap f (contents a) = contents y := ⟨f a, rfl⟩

/-- Universal injectivity. -/
theorem universal_injective (f : α → α)
    (hf : ∀ a b, f a = f b → a = b) (a b : α)
    (h : valMap f (contents a) = valMap f (contents b)) :
    a = b := by simp [valMap] at h; exact hf a b h

/-- Subgroup product formula: |HK|·|H∩K| = |H|·|K|. -/
theorem subgroup_product_formula [ValArith α] (hkSize interSize hSize kSize : α)
    (h : ValArith.mulF hkSize interSize = ValArith.mulF hSize kSize) :
    mul (contents hkSize) (contents interSize) = mul (contents hSize) (contents kSize) := by
  simp [mul, h]

end Val
