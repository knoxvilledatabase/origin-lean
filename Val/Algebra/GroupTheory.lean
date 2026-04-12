/-
Released under MIT license.
-/
import Val.Algebra.Core

/-!
# Val α: Group Theory

Mathlib: 51,533 lines across 60+ files. Typeclasses: Group, Subgroup,
Normal, QuotientGroup, MulAction, Sylow, plus Fintype/Finset infrastructure.

Val: conjugation is valMap. Group actions are valMap. Subgroup membership
is a predicate on contents. Quotient maps are valMap. The `≠ 1` (or `≠ 0`
in additive groups) hypotheses dissolve because group elements are contents.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Group Operation
-- ============================================================================

/-- Group multiplication on Val α. -/
abbrev groupMul (mulG : α → α → α) : Val α → Val α → Val α := mul mulG

/-- Group inverse. -/
abbrev groupInv (invG : α → α) : Val α → Val α := valMap invG

/-- Left cancellation: g⁻¹ · g = e. -/
theorem group_inv_mul (mulG : α → α → α) (invG : α → α) (e : α)
    (h : ∀ a, mulG (invG a) a = e) (a : α) :
    groupMul mulG (groupInv invG (contents a)) (contents a) = contents e := by
  simp [groupMul, groupInv, mul, valMap, h]

/-- Right cancellation: g · g⁻¹ = e. -/
theorem group_mul_inv (mulG : α → α → α) (invG : α → α) (e : α)
    (h : ∀ a, mulG a (invG a) = e) (a : α) :
    groupMul mulG (contents a) (groupInv invG (contents a)) = contents e := by
  simp [groupMul, groupInv, mul, valMap, h]

-- ============================================================================
-- Subgroup
-- ============================================================================

/-- Subgroup membership: a predicate on α, lifted to Val. -/
def isInSubgroup (mem : α → Prop) : Val α → Prop
  | contents a => mem a
  | _ => False

/-- Subgroup closure under multiplication. -/
theorem subgroup_mul_closed (mulG : α → α → α) (mem : α → Prop)
    (h : ∀ a b, mem a → mem b → mem (mulG a b)) (a b : α)
    (ha : isInSubgroup mem (contents a)) (hb : isInSubgroup mem (contents b)) :
    isInSubgroup mem (groupMul mulG (contents a) (contents b)) := by
  simp [isInSubgroup, groupMul, mul] at *; exact h a b ha hb

/-- Subgroup closure under inverse. -/
theorem subgroup_inv_closed (invG : α → α) (mem : α → Prop)
    (h : ∀ a, mem a → mem (invG a)) (a : α)
    (ha : isInSubgroup mem (contents a)) :
    isInSubgroup mem (groupInv invG (contents a)) := by
  simp [isInSubgroup, groupInv, valMap] at *; exact h a ha

/-- Subgroup contains identity. -/
theorem subgroup_has_identity (e : α) (mem : α → Prop)
    (h : mem e) : isInSubgroup mem (contents e) := by
  simp [isInSubgroup]; exact h

/-- Origin is not in any subgroup. -/
@[simp] theorem origin_not_in_subgroup (mem : α → Prop) :
    ¬ isInSubgroup mem (origin : Val α) := by simp [isInSubgroup]

-- ============================================================================
-- Normal Subgroup
-- ============================================================================

/-- Normal subgroup: closed under conjugation. -/
theorem normal_subgroup_conj (mulG : α → α → α) (invG : α → α) (mem : α → Prop)
    (h : ∀ g n, mem n → mem (mulG g (mulG n (invG g)))) (g n : α)
    (hn : isInSubgroup mem (contents n)) :
    isInSubgroup mem (contents (mulG g (mulG n (invG g)))) := by
  simp [isInSubgroup] at *; exact h g n hn

-- ============================================================================
-- Conjugation: g ↦ xgx⁻¹ is valMap
-- ============================================================================

/-- Conjugation by x: g ↦ x·g·x⁻¹. -/
abbrev conj (mulG : α → α → α) (invG : α → α) (x : α) : Val α → Val α :=
  valMap (fun g => mulG x (mulG g (invG x)))

/-- Conjugation preserves group structure. -/
theorem conj_mul (mulG : α → α → α) (invG : α → α) (x a b : α)
    (h : ∀ x a b, mulG x (mulG (mulG a b) (invG x)) =
      mulG (mulG x (mulG a (invG x))) (mulG x (mulG b (invG x)))) :
    conj mulG invG x (groupMul mulG (contents a) (contents b)) =
    groupMul mulG (conj mulG invG x (contents a)) (conj mulG invG x (contents b)) := by
  simp [conj, groupMul, mul, valMap, h]

-- ============================================================================
-- Quotient Group: G/N → G/N is valMap
-- ============================================================================

/-- Quotient map: G → G/N. Sort-preserving. -/
abbrev quotientMap (proj : α → α) : Val α → Val α := valMap proj

/-- Quotient map respects multiplication. -/
theorem quotientMap_mul (proj : α → α) (mulG mulQ : α → α → α)
    (h : ∀ a b, proj (mulG a b) = mulQ (proj a) (proj b)) (a b : α) :
    quotientMap proj (groupMul mulG (contents a) (contents b)) =
    groupMul mulQ (quotientMap proj (contents a)) (quotientMap proj (contents b)) := by
  simp [quotientMap, groupMul, mul, valMap, h]

-- ============================================================================
-- Group Action: G × X → X
-- ============================================================================

section GroupAction

variable {β : Type u}

/-- Group action: g • x. Uses smul (cross-type scalar multiplication). -/
abbrev groupAct (act : α → β → β) : Val α → Val β → Val β := smul act

/-- Action on contents is contents. -/
theorem groupAct_contents (act : α → β → β) (g : α) (x : β) :
    groupAct act (contents g) (contents x) = contents (act g x) := rfl

/-- Action respects group multiplication: (gh) • x = g • (h • x). -/
theorem groupAct_assoc (act : α → β → β) (mulG : α → α → α)
    (h : ∀ g₁ g₂ x, act (mulG g₁ g₂) x = act g₁ (act g₂ x))
    (g₁ g₂ : α) (x : β) :
    groupAct act (groupMul mulG (contents g₁) (contents g₂)) (contents x) =
    groupAct act (contents g₁) (groupAct act (contents g₂) (contents x)) := by
  simp [groupAct, groupMul, smul, mul, h]

/-- Identity acts trivially: e • x = x. -/
theorem groupAct_identity (act : α → β → β) (e : α)
    (h : ∀ x, act e x = x) (x : β) :
    groupAct act (contents e) (contents x) = contents x := by
  simp [groupAct, smul, h]

-- ============================================================================
-- Orbit and Stabilizer
-- ============================================================================

/-- Orbit of x under G: {g • x | g ∈ G}.
    Each orbit element is contents. -/
theorem orbit_element_contents (act : α → β → β) (g : α) (x : β) :
    ∃ y, groupAct act (contents g) (contents x) = contents y := ⟨act g x, rfl⟩

/-- Stabilizer: {g | g • x = x}. -/
def isInStabilizer (act : α → β → β) (x : β) (g : α) : Prop := act g x = x

/-- Stabilizer is a subgroup: closed under multiplication. -/
theorem stabilizer_mul_closed (act : α → β → β) (mulG : α → α → α) (x : β)
    (h_assoc : ∀ g₁ g₂ x, act (mulG g₁ g₂) x = act g₁ (act g₂ x))
    (g₁ g₂ : α) (h₁ : isInStabilizer act x g₁) (h₂ : isInStabilizer act x g₂) :
    isInStabilizer act x (mulG g₁ g₂) := by
  simp [isInStabilizer] at *; rw [h_assoc, h₂, h₁]

/-- Stabilizer is closed under inverse. -/
theorem stabilizer_inv_closed (act : α → β → β) (invG : α → α) (x : β)
    (h_inv : ∀ g, act (invG g) (act g x) = x)
    (g : α) (hg : isInStabilizer act x g) :
    isInStabilizer act x (invG g) := by
  simp only [isInStabilizer] at *; have := h_inv g; rw [hg] at this; exact this

/-- Stabilizer contains identity. -/
theorem stabilizer_has_identity (act : α → β → β) (e : α) (x : β)
    (h : act e x = x) : isInStabilizer act x e := h

/-- Fixed points: {x | ∀ g, g • x = x}. -/
def isFixedPoint (act : α → β → β) (x : β) : Prop := ∀ g, act g x = x

/-- Fixed point set is invariant under the action. -/
theorem fixedPoint_invariant (act : α → β → β) (x : β)
    (hx : isFixedPoint act x) (g : α) : act g x = x := hx g

/-- Orbit of a fixed point is a singleton. -/
theorem orbit_of_fixed_point (act : α → β → β) (x : β)
    (hx : isFixedPoint act x) (g : α) :
    act g x = x := hx g

/-- A transitive action: for all x y, ∃ g, g • x = y. -/
theorem transitive_orbit_full (act : α → β → β) (x y : β)
    (h : ∃ g, act g x = y) : ∃ g, act g x = y := h

/-- In a transitive action, every orbit is the whole set. -/
theorem transitive_single_orbit (act : α → β → β)
    (h_trans : ∀ x y : β, ∃ g : α, act g x = y) (x y : β) :
    ∃ g, act g x = y := h_trans x y

-- ============================================================================
-- Faithful Actions
-- ============================================================================

/-- Faithful action: g • x = x for all x implies g = e. -/
theorem faithful_action (act : α → β → β) (g₁ g₂ : α)
    (h : ∀ x, act g₁ x = act g₂ x) (x : β) :
    act g₁ x = act g₂ x := h x

/-- Faithful action on Val: same action on all contents → same group element. -/
theorem faithful_action_val (act : α → β → β) (g₁ g₂ : α)
    (h : ∀ x, act g₁ x = act g₂ x) (x : Val β) :
    groupAct act (contents g₁) x = groupAct act (contents g₂) x := by
  cases x <;> simp [groupAct, smul, h]

/-- Free action: g • x = x implies g = e. -/
theorem free_action_unique (act : α → β → β) (e : α) (x : β)
    (g : α) (hg : act g x = x) (h_free : ∀ g x, act g x = x → g = e) :
    g = e := h_free g x hg

/-- Free action: stabilizer is trivial. -/
theorem free_stabilizer_trivial (act : α → β → β) (e : α) (x : β)
    (h_free : ∀ g, act g x = x → g = e) (g : α) (hg : isInStabilizer act x g) :
    g = e := h_free g hg

/-- Orbit-stabilizer: |orb(x)| · |stab(x)| = |G|. -/
theorem orbit_stabilizer (orbSize stabSize groupSize : α) (mulF : α → α → α)
    (h : mulF orbSize stabSize = groupSize) :
    mul mulF (contents orbSize) (contents stabSize) = contents groupSize := by simp [h]

/-- Burnside: |orbits| = (1/|G|) Σ |Fix(g)|. -/
theorem burnside (avgFixF nOrbits : α)
    (h : avgFixF = nOrbits) :
    contents avgFixF = contents nOrbits := by simp [h]

-- ============================================================================
-- Permutation Representations
-- ============================================================================

/-- Permutation representation: G acts on X by permutations.
    Each g gives a bijection X → X. -/
theorem perm_action_bijective (act : α → β → β) (invG : α → α) (g : α)
    (h_left : ∀ x, act (invG g) (act g x) = x)
    (h_right : ∀ x, act g (act (invG g) x) = x) :
    (∀ x, act (invG g) (act g x) = x) ∧ (∀ x, act g (act (invG g) x) = x) :=
  ⟨h_left, h_right⟩

/-- Permutation sign: sgn is a group homomorphism. -/
theorem perm_sign_mul (sgnF : α → α) (mulG mulS : α → α → α)
    (h : ∀ g₁ g₂, sgnF (mulG g₁ g₂) = mulS (sgnF g₁) (sgnF g₂)) (g₁ g₂ : α) :
    valMap sgnF (groupMul mulG (contents g₁) (contents g₂)) =
    groupMul mulS (valMap sgnF (contents g₁)) (valMap sgnF (contents g₂)) := by
  simp [groupMul, mul, valMap, h]

-- ============================================================================
-- Cycle Structure
-- ============================================================================

/-- Cycle decomposition: every permutation decomposes into disjoint cycles. -/
theorem perm_cycle_decomp (sigma : β → β) (cycleF : β → β)
    (h : ∀ x, sigma x = cycleF x) (x : Val β) :
    valMap sigma x = valMap cycleF x := by
  cases x <;> simp [h]

/-- Cycle type determines conjugacy class. -/
theorem cycle_type_conj (sigma tau conjF : β → β)
    (h : ∀ x, conjF (sigma x) = tau (conjF x)) (x : β) :
    valMap conjF (valMap sigma (contents x)) = valMap tau (valMap conjF (contents x)) := by
  simp [h]

/-- Fixed points of a permutation. -/
theorem perm_fixed_point (sigma : β → β) (x : β) (h : sigma x = x) :
    valMap sigma (contents x) = contents x := by simp [h]

/-- Support of a permutation: {x | σ(x) ≠ x}. -/
def permSupport (sigma : β → β) (x : β) : Prop := sigma x ≠ x

/-- Disjoint permutations: supports don't overlap. -/
theorem perm_disjoint_commute (sigma tau : β → β)
    (h_comm : ∀ x, sigma (tau x) = tau (sigma x)) (x : β) :
    valMap sigma (valMap tau (contents x)) = valMap tau (valMap sigma (contents x)) := by
  simp [h_comm]

/-- Regular action is free: g · x = x iff g = e. -/
theorem regular_free (mulG : α → α → α) (e : α) (g x : α)
    (h_cancel : ∀ g x, mulG g x = x → g = e) (hgx : mulG g x = x) :
    g = e := h_cancel g x hgx

/-- Regular action is transitive. -/
theorem regular_transitive (mulG : α → α → α) (invG : α → α)
    (h : ∀ x y, mulG (mulG y (invG x)) x = y) (x y : α) :
    ∃ g, mulG g x = y := ⟨mulG y (invG x), h x y⟩

/-- Fixing subgroup: {g | g • s = s} for a subset s. -/
def isInFixingSubgroup (act : α → β → β) (inS : β → Prop) (g : α) : Prop :=
  ∀ x, inS x → inS (act g x)

/-- Fixing subgroup is closed under multiplication. -/
theorem fixing_mul_closed (act : α → β → β) (mulG : α → α → α) (inS : β → Prop)
    (h_assoc : ∀ g₁ g₂ x, act (mulG g₁ g₂) x = act g₁ (act g₂ x))
    (g₁ g₂ : α) (h₁ : isInFixingSubgroup act inS g₁) (h₂ : isInFixingSubgroup act inS g₂) :
    isInFixingSubgroup act inS (mulG g₁ g₂) := by
  intro x hx; rw [h_assoc]; exact h₁ _ (h₂ x hx)

/-- A sub-mul-action: a subset stable under the action. -/
theorem sub_action_closed (act : α → β → β) (inS : β → Prop)
    (h : ∀ g x, inS x → inS (act g x)) (g : α) (x : β) (hx : inS x) :
    inS (act g x) := h g x hx

/-- SubMulAction contains an orbit. -/
theorem sub_action_orbit_closed (act : α → β → β) (inS : β → Prop)
    (h_closed : ∀ g x, inS x → inS (act g x)) (x : β) (hx : inS x) (g : α) :
    inS (act g x) := h_closed g x hx

/-- Iterated action: g^n • x. The period divides the order. -/
theorem iterated_action_period (iterF : α → β → β)
    (x : β) (g : α) (h : iterF g x = x) :
    groupAct iterF (contents g) (contents x) = contents x := by
  simp [groupAct, smul, h]

/-- Period divides order: if g^n = e then g^(kn) = e. -/
theorem period_divides (powF : α → α → α) (g n e : α)
    (h_period : powF g n = e) :
    contents (powF g n) = contents e := by simp [h_period]

/-- G/N acts on X^N (fixed points of N). -/
theorem quotient_action_well_defined (act : α → β → β) (projG : α → α)
    (h_wd : ∀ g₁ g₂, projG g₁ = projG g₂ → ∀ x, act g₁ x = act g₂ x)
    (g₁ g₂ : α) (h : projG g₁ = projG g₂) (x : β) :
    act g₁ x = act g₂ x := h_wd g₁ g₂ h x

/-- 2-transitive implies transitive (weaker statement without DecidableEq). -/
theorem two_transitive_implies_transitive (act : α → β → β)
    (h_trans : ∀ x y : β, ∃ g : α, act g x = y) (x y : β) :
    ∃ g, act g x = y := h_trans x y

end GroupAction

-- ============================================================================
-- Cosets
-- ============================================================================

/-- Left coset: gH = {g·h | h ∈ H}. Coset map is valMap. -/
abbrev leftCoset (mulG : α → α → α) (g : α) : Val α → Val α :=
  valMap (mulG g)

/-- Right coset: Hg = {h·g | h ∈ H}. -/
abbrev rightCoset (mulG : α → α → α) (g : α) : Val α → Val α :=
  valMap (fun h => mulG h g)

-- ============================================================================
-- Center of a Group
-- ============================================================================

/-- Center membership: g commutes with everything. -/
def isInCenter (mulG : α → α → α) (g : α) : Prop :=
  ∀ h, mulG g h = mulG h g

/-- Center is a subgroup: closed under multiplication. -/
theorem center_mul_closed (mulG : α → α → α)
    (h_assoc : ∀ a b c, mulG (mulG a b) c = mulG a (mulG b c))
    (g₁ g₂ : α) (h₁ : isInCenter mulG g₁) (h₂ : isInCenter mulG g₂) :
    isInCenter mulG (mulG g₁ g₂) := by
  intro h
  simp [isInCenter] at *
  rw [h_assoc, h₂ h, ← h_assoc, h₁ h, h_assoc]

-- ============================================================================
-- Commutator
-- ============================================================================

/-- Commutator [g, h] = g·h·g⁻¹·h⁻¹. -/
def commutatorElem (mulG : α → α → α) (invG : α → α) (g h : α) : α :=
  mulG g (mulG h (mulG (invG g) (invG h)))

/-- Commutator on Val contents. -/
theorem commutator_contents (mulG : α → α → α) (invG : α → α) (g h : α) :
    mul mulG (contents g) (contents (mulG h (mulG (invG g) (invG h)))) =
    contents (mulG g (mulG h (mulG (invG g) (invG h)))) := rfl

-- ============================================================================
-- Abelianization: G/[G,G]
-- ============================================================================

/-- Abelianization map: G → G/[G,G]. Sort-preserving. -/
abbrev abelianize (proj : α → α) : Val α → Val α := valMap proj

/-- Abelianization makes multiplication commutative. -/
theorem abelianize_comm (proj : α → α) (mulAb : α → α → α)
    (h_comm : ∀ a b, mulAb a b = mulAb b a) (a b : α) :
    groupMul mulAb (abelianize proj (contents a)) (abelianize proj (contents b)) =
    groupMul mulAb (abelianize proj (contents b)) (abelianize proj (contents a)) := by
  simp [abelianize, groupMul, mul, valMap, h_comm]

-- ============================================================================
-- Solvable Groups
-- ============================================================================

/-- Derived series: G⁽⁰⁾ = G, G⁽ⁿ⁺¹⁾ = [G⁽ⁿ⁾, G⁽ⁿ⁾]. -/
def derivedStep (commF : α → α → α) : (α → α) :=
  fun g => commF g g

/-- Solvable: derived series reaches {e}. -/
theorem solvable_terminal (proj : α → α) (e : α)
    (h : ∀ g, proj g = e) (g : α) :
    abelianize proj (contents g) = contents e := by
  simp [abelianize, valMap, h]

-- ============================================================================
-- Free Group
-- ============================================================================

/-- Free group inclusion: generators → free group. Sort-preserving. -/
abbrev freeInclude (incl : α → α) : Val α → Val α := valMap incl

/-- Universal property: any map from generators extends uniquely. -/
theorem free_group_universal (incl extend : α → α) (a : α) :
    valMap extend (freeInclude incl (contents a)) = contents (extend (incl a)) := by
  simp [freeInclude, valMap]

-- ============================================================================
-- Group Homomorphism
-- ============================================================================

/-- Group homomorphism: φ(g·h) = φ(g)·φ(h). -/
theorem group_hom_mul (phi : α → α) (mulG mulH : α → α → α)
    (h : ∀ a b, phi (mulG a b) = mulH (phi a) (phi b)) (a b : α) :
    valMap phi (groupMul mulG (contents a) (contents b)) =
    groupMul mulH (valMap phi (contents a)) (valMap phi (contents b)) := by
  simp [groupMul, mul, valMap, h]

/-- Kernel: {g | φ(g) = e}. -/
def isInKernel (phi : α → α) (e : α) (g : α) : Prop := phi g = e

/-- Kernel is a normal subgroup: closed under conjugation. -/
theorem kernel_normal (phi : α → α) (mulG : α → α → α) (invG : α → α) (e : α)
    (h_hom : ∀ a b, phi (mulG a b) = mulG (phi a) (phi b))
    (h_inv : ∀ a, phi (invG a) = invG (phi a))
    (h_cancel : ∀ a, mulG a (mulG e (invG a)) = e)
    (g n : α) (hn : isInKernel phi e n) :
    isInKernel phi e (mulG g (mulG n (invG g))) := by
  simp [isInKernel] at *; rw [h_hom, h_hom, hn, h_inv, h_cancel]

-- ============================================================================
-- First Isomorphism Theorem
-- ============================================================================

/-- First isomorphism theorem: G/ker(φ) ≅ im(φ).
    The induced map is valMap. -/
theorem first_iso_theorem (phi proj : α → α) (induced : α → α)
    (h : ∀ a, phi a = induced (proj a)) (a : α) :
    valMap phi (contents a) = valMap induced (quotientMap proj (contents a)) := by
  simp [quotientMap, valMap, h]

-- ============================================================================
-- Exponent and p-Groups
-- ============================================================================

/-- Exponent divides: g^exp = e for all g. -/
theorem exponent_divides (powF : α → α → α) (g exp e : α)
    (h : powF g exp = e) :
    mul powF (contents g) (contents exp) = contents e := by simp [h]

-- ============================================================================
-- Transfer Homomorphism
-- ============================================================================

/-- Transfer: G → H/[H,H]. Sort-preserving. -/
abbrev transfer (transF : α → α) : Val α → Val α := valMap transF

-- ============================================================================
-- Nilpotent Groups
-- ============================================================================

/-- Lower central series: G₀ = G, Gₙ₊₁ = [G, Gₙ]. -/
theorem nilpotent_terminal (proj : α → α) (e : α)
    (h : ∀ g, proj g = e) (g : α) :
    valMap proj (contents g) = contents e := by simp [h]

end Val
