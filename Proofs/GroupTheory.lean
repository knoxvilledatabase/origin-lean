/-
Released under MIT license.
-/
import Origin.Core
import Origin.GroupTheory

/-!
# Proof: Group theory works with Origin

The rebound. Groups, subgroups, homomorphisms, conjugacy — the
structural algebra that sits between field axioms and analysis.

Every theorem uses Origin's GroupAxioms and Core's Option instances.
No Mathlib. If groups work on Option α, the machinery is solid.
-/

universe u
variable {α : Type u}

-- ============================================================================
-- 1. GROUP AXIOMS LIFT THROUGH OPTION
-- ============================================================================

-- Associativity lifts
theorem group_mul_assoc [Mul α] (h : ∀ a b c : α, a * b * c = a * (b * c))
    (a b c : Option α) : a * b * c = a * (b * c) :=
  option_mul_assoc h a b c

-- Identity: none is the multiplicative absorber, not identity.
-- The group identity is some(e), inside the counting domain.
-- This is the key distinction Origin makes.
theorem group_left_id [Mul α] (e : α) (h : ∀ a : α, e * a = a) (a : α) :
    (some e : Option α) * some a = some a := by simp [h]

theorem group_right_id [Mul α] (e : α) (h : ∀ a : α, a * e = a) (a : α) :
    (some a : Option α) * some e = some a := by simp [h]

-- Inverse: some a * some (-a) = some(e), stays in counting domain
theorem group_left_inv [Mul α] [Neg α] (e : α)
    (h : ∀ a : α, (-a) * a = e) (a : α) :
    (some (-a) : Option α) * some a = some e := by simp [h]

-- none absorbs — the ground is not a group element
theorem group_none_absorbs [Mul α] (a : Option α) :
    none * a = none := mul_none_left a

-- ============================================================================
-- 2. HOMOMORPHISMS LIFT THROUGH OPTION
-- ============================================================================

-- A group homomorphism preserves multiplication
-- Mathlib: MonoidHom. Origin: just a function with a property.
theorem hom_preserves [Mul α] (f : α → α)
    (h : ∀ a b, f (a * b) = f a * f b) (a b : α) :
    Option.map f (some a * some b) =
    Option.map f (some a) * Option.map f (some b) := by simp [h]

-- Homomorphisms map none to none — the ground is preserved
theorem hom_none (f : α → α) :
    Option.map f (none : Option α) = none := rfl

-- Composition of homomorphisms
theorem hom_comp [Mul α] (f g : α → α)
    (hf : ∀ a b, f (a * b) = f a * f b)
    (hg : ∀ a b, g (a * b) = g a * g b) (a b : α) :
    Option.map (g ∘ f) (some a * some b) =
    Option.map (g ∘ f) (some a) * Option.map (g ∘ f) (some b) := by
  simp [Function.comp, hf, hg]

-- Identity homomorphism
theorem hom_id [Mul α] (a : Option α) :
    Option.map id a = a := by cases a <;> simp

-- ============================================================================
-- 3. SUBGROUPS
-- ============================================================================

-- A subgroup lifts to Option via liftPred
theorem subgroup_lift [Mul α] [Neg α] (mem : α → Prop) (e : α)
    (hsub : isSubgroup mem e) (a : α) (ha : mem a) :
    liftPred mem (some a) := by simp [ha]

-- The ground is never in a subgroup (predicates are for parts)
theorem subgroup_none [Mul α] [Neg α] (mem : α → Prop) :
    ¬liftPred mem (none : Option α) := by simp

-- Subgroup closure under multiplication
theorem subgroup_mul_closed [Mul α] [Neg α] (mem : α → Prop) (e : α)
    (hsub : isSubgroup mem e) (a b : α) (ha : mem a) (hb : mem b) :
    mem (a * b) :=
  hsub.2.1 a b ha hb

-- Subgroup closure under inverse
theorem subgroup_inv_closed [Mul α] [Neg α] (mem : α → Prop) (e : α)
    (hsub : isSubgroup mem e) (a : α) (ha : mem a) :
    mem (-a) :=
  hsub.2.2 a ha

-- ============================================================================
-- 4. NORMAL SUBGROUPS AND CONJUGACY
-- ============================================================================

-- Conjugacy lifts: g * a * (-g) on some values
theorem conjugate_some [Mul α] [Neg α] (g a : α) :
    (some g : Option α) * some a * -(some g) = some (g * a * -g) := by simp

-- Conjugacy absorbs at none: none * anything * anything = none
theorem conjugate_none_left [Mul α] [Neg α] (a : Option α) :
    (none : Option α) * a * -(none : Option α) = none := by simp

-- Normal subgroup: closed under conjugation (on some values)
theorem normal_conjugate [Mul α] [Neg α] (mem : α → Prop)
    (hnorm : isNormal mem) (g a : α) (ha : mem a) :
    mem (g * a * -g) :=
  hnorm g a ha

-- ============================================================================
-- 5. COSETS
-- ============================================================================

-- Coset equivalence is reflexive
theorem coset_refl [Mul α] [Neg α] (mem : α → Prop) (e : α)
    (hcancel : ∀ a : α, -a * a = e) (he : mem e) (a : α) :
    cosetEquiv mem a a :=
  cosetEquiv_refl mem e hcancel he a

-- ============================================================================
-- 6. COMMUTATOR
-- ============================================================================

-- The commutator [a,b] = a * b * (-a) * (-b)
theorem commutator_def [Mul α] [Neg α] (a b : α) :
    commutator a b = a * b * -a * -b := rfl

-- Commutator on Option: some values compute, none absorbs
theorem commutator_some [Mul α] [Neg α] (a b : α) :
    (some (commutator a b) : Option α) = some (a * b * -a * -b) := rfl

-- ============================================================================
-- 7. ABELIAN GROUPS
-- ============================================================================

-- Abelian: commutativity lifts through Option
theorem abelian_option [Mul α] (h : isAbelian (α := α))
    (a b : Option α) : a * b = b * a :=
  option_mul_comm h a b

-- In an abelian group, the commutator is the identity
-- In an abelian group, commutator a b = a * b * (-a) * (-b).
-- With commutativity: a * b * (-a) * (-b) = a * (-a) * b * (-b) = e * e = e.
-- The full proof needs neg_mul distributivity — stated as a property.
theorem abelian_commutator_trivial [Mul α] [Neg α] (e : α)
    (hcomm : ∀ a b : α, a * b = b * a)
    (hassoc : ∀ a b c : α, a * b * c = a * (b * c))
    (hrinv : ∀ a : α, a * (-a) = e)
    (hrid : ∀ a : α, a * e = a)
    (hneg_distrib : ∀ a b : α, -(a * b) = -a * -b)
    (a b : α) :
    commutator a b = e := by
  simp [commutator]
  calc a * b * -a * -b
      _ = a * b * (-a * -b)     := by rw [hassoc]
      _ = a * b * -(a * b)      := by rw [← hneg_distrib]
      _ = e                     := by rw [hrinv]

-- ============================================================================
-- 8. GROUP ACTION
-- ============================================================================

-- Group action identity
theorem action_id [Mul α] (act : α → α → α) (e : α)
    (hact : isGroupAction act e) (x : α) :
    act e x = x :=
  hact.1 x

-- Group action compatibility
theorem action_compat [Mul α] (act : α → α → α) (e : α)
    (hact : isGroupAction act e) (g h x : α) :
    act g (act h x) = act (g * h) x :=
  hact.2 g h x

-- Action lifts through Option
theorem action_option (act : α → α) (v : Option α) :
    Option.map act v = match v with | none => none | some a => some (act a) := by
  cases v <;> simp

-- ============================================================================
-- 9. CONCRETE: Option Int as a group under addition
-- ============================================================================

-- Int addition is a group
example : (some 3 : Option Int) + some 5 = some 8 := rfl
example : (some 3 : Option Int) + -(some 3) = some 0 := by simp
example : (none : Option Int) + some 5 = some 5 := rfl
example : (some 5 : Option Int) + none = some 5 := by simp

-- Cancellation stays in the counting domain
-- 3 + (-3) = some 0, NOT none. The zero measurement, not the ground.
theorem int_cancel : (some 3 : Option Int) + -(some 3) = some 0 := by simp

-- The ground absorbs under multiplication
theorem int_absorb : (none : Option Int) * some 5 = none := rfl

-- These are different!
theorem cancel_ne_absorb : (some 0 : Option Int) ≠ (none : Option Int) := by simp
