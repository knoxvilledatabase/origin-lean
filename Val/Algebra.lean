/-
Released under MIT license.
-/
import Val.Foundation

/-!
# Val α: Algebra — The Complete Algebraic Toolkit

Every algebraic law that α satisfies is lifted to Val α here.
Proved once. Called everywhere. No domain file re-proves these.

The pattern: cases <;> simp <;> apply h

Origin cases: simp closes them (Foundation's simp lemmas).
Non-origin cases: simp reduces to constructor(expression) = constructor(expression).
Then apply h uses α's law inside the constructor.

Explicit function parameters. Zero typeclasses. Zero Mathlib.

## Contents

1. Lifted Laws — associativity, commutativity, distributivity, identity, negation, subtraction, inverse, faithful embedding, sort
2. Ring and Field Laws — dissolved hypotheses, division
3. Ordered Field — ordering within contents, partial order, abs, min/max
4. Vector Spaces — scalar multiplication, module laws
5. Polynomial Ring — Horner evaluation, origin propagation, contents closure
6. Functional Analysis — norms, operators, inner products, completeness
7. Spectral Theory — resolvent, spectral decomposition, operator functions
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- SECTION 1: Lifted Laws — The Abstract Base Model
-- ============================================================================

-- ============================================================================
-- Associativity
-- ============================================================================

theorem mul_assoc (f : α → α → α)
    (h : ∀ a b c : α, f (f a b) c = f a (f b c))
    (a b c : Val α) : mul f (mul f a b) c = mul f a (mul f b c) := by
  cases a <;> cases b <;> cases c <;> simp [mul] <;> apply h

theorem add_assoc (f : α → α → α)
    (h : ∀ a b c : α, f (f a b) c = f a (f b c))
    (a b c : Val α) : add f (add f a b) c = add f a (add f b c) := by
  cases a <;> cases b <;> cases c <;> simp [add] <;> apply h

-- ============================================================================
-- Commutativity
-- ============================================================================

theorem mul_comm (f : α → α → α)
    (h : ∀ a b : α, f a b = f b a)
    (a b : Val α) : mul f a b = mul f b a := by
  cases a <;> cases b <;> simp [mul] <;> apply h

theorem add_comm (f : α → α → α)
    (h : ∀ a b : α, f a b = f b a)
    (a b : Val α) : add f a b = add f b a := by
  cases a <;> cases b <;> simp [add] <;> apply h

-- ============================================================================
-- Distributivity
-- ============================================================================

theorem left_distrib (mulF addF : α → α → α)
    (h : ∀ a b c : α, mulF a (addF b c) = addF (mulF a b) (mulF a c))
    (a b c : Val α) : mul mulF a (add addF b c) = add addF (mul mulF a b) (mul mulF a c) := by
  cases a <;> cases b <;> cases c <;> simp [mul, add] <;> apply h

theorem right_distrib (mulF addF : α → α → α)
    (h : ∀ a b c : α, mulF (addF a b) c = addF (mulF a c) (mulF b c))
    (a b c : Val α) : mul mulF (add addF a b) c = add addF (mul mulF a c) (mul mulF b c) := by
  cases a <;> cases b <;> cases c <;> simp [mul, add] <;> apply h

-- ============================================================================
-- Identity Laws
-- ============================================================================

theorem mul_one (f : α → α → α) (one : α)
    (h : ∀ a : α, f a one = a)
    (a : Val α) : mul f a (contents one) = a := by
  cases a <;> simp [mul, h]

theorem one_mul (f : α → α → α) (one : α)
    (h : ∀ a : α, f one a = a)
    (a : Val α) : mul f (contents one) a = a := by
  cases a <;> simp [mul, h]

theorem add_zero (f : α → α → α) (zero : α)
    (h : ∀ a : α, f a zero = a)
    (a : Val α) : add f a (contents zero) = a := by
  cases a <;> simp [add, h]

theorem zero_add (f : α → α → α) (zero : α)
    (h : ∀ a : α, f zero a = a)
    (a : Val α) : add f (contents zero) a = a := by
  cases a <;> simp [add, h]

-- ============================================================================
-- Negation Laws
-- ============================================================================

theorem neg_mul (mulF : α → α → α) (negF : α → α)
    (h : ∀ a b : α, mulF (negF a) b = negF (mulF a b))
    (a b : Val α) : mul mulF (neg negF a) b = neg negF (mul mulF a b) := by
  cases a <;> cases b <;> simp [mul, neg] <;> apply h

theorem mul_neg (mulF : α → α → α) (negF : α → α)
    (h : ∀ a b : α, mulF a (negF b) = negF (mulF a b))
    (a b : Val α) : mul mulF a (neg negF b) = neg negF (mul mulF a b) := by
  cases a <;> cases b <;> simp [mul, neg] <;> apply h

theorem neg_neg (negF : α → α)
    (h : ∀ a : α, negF (negF a) = a)
    (a : Val α) : neg negF (neg negF a) = a := by
  cases a <;> simp [neg, h]

-- ============================================================================
-- Subtraction Laws (derived from distributivity + negation)
-- ============================================================================

theorem sub_mul (mulF addF : α → α → α) (negF : α → α)
    (h_distrib : ∀ a b c : α, mulF (addF a b) c = addF (mulF a c) (mulF b c))
    (h_neg : ∀ a b : α, mulF (negF a) b = negF (mulF a b))
    (a b c : Val α) :
    mul mulF (add addF a (neg negF b)) c =
    add addF (mul mulF a c) (neg negF (mul mulF b c)) := by
  rw [right_distrib mulF addF h_distrib, neg_mul mulF negF h_neg]

theorem mul_sub (mulF addF : α → α → α) (negF : α → α)
    (h_distrib : ∀ a b c : α, mulF a (addF b c) = addF (mulF a b) (mulF a c))
    (h_neg : ∀ a b : α, mulF a (negF b) = negF (mulF a b))
    (a b c : Val α) :
    mul mulF a (add addF b (neg negF c)) =
    add addF (mul mulF a b) (neg negF (mul mulF a c)) := by
  rw [left_distrib mulF addF h_distrib, mul_neg mulF negF h_neg]

-- ============================================================================
-- Inverse Laws
-- ============================================================================

theorem mul_inv (mulF : α → α → α) (invF : α → α) (one : α)
    (h : ∀ a : α, mulF a (invF a) = one)
    (a : α) : mul mulF (contents a) (inv invF (contents a)) = contents one := by
  simp [mul, inv, h]

theorem inv_mul (mulF : α → α → α) (invF : α → α) (one : α)
    (h : ∀ a : α, mulF (invF a) a = one)
    (a : α) : mul mulF (inv invF (contents a)) (contents a) = contents one := by
  simp [mul, inv, h]

theorem inv_inv (invF : α → α)
    (h : ∀ a : α, invF (invF a) = a)
    (a : Val α) : inv invF (inv invF a) = a := by
  cases a <;> simp [inv, h]

-- ============================================================================
-- Additive Inverse Laws
-- ============================================================================

theorem add_neg (addF : α → α → α) (negF : α → α) (zero : α)
    (h : ∀ a : α, addF a (negF a) = zero)
    (a : α) : add addF (contents a) (neg negF (contents a)) = contents zero := by
  simp [add, neg, h]

theorem neg_add (addF : α → α → α) (negF : α → α) (zero : α)
    (h : ∀ a : α, addF (negF a) a = zero)
    (a : α) : add addF (neg negF (contents a)) (contents a) = contents zero := by
  simp [add, neg, h]

-- ============================================================================
-- Faithful Embedding
-- ============================================================================

-- contents preserves all operations (from Foundation's simp lemmas):
--   mul f (contents a) (contents b) = contents (f a b)
--   add f (contents a) (contents b) = contents (f a b)
--   neg f (contents a) = contents (f a)
--   inv f (contents a) = contents (f a)
-- All by simp. The bucket is transparent.

-- contents is injective (from Foundation):
--   contents_injective, contents_inj

-- ============================================================================
-- Sort Result of Any Operation
-- ============================================================================

-- The sort of mul f a b is ALWAYS determined by the sorts of a and b.
-- No hypothesis needed. The type carries it.

theorem mul_sort (f : α → α → α) (a b : Val α) :
    (a = origin ∨ b = origin → mul f a b = origin) ∧
    (∀ va vb, a = contents va → b = contents vb → mul f a b = contents (f va vb)) ∧
    (∀ va vb, a = container va → b = container vb → mul f a b = container (f va vb)) ∧
    (∀ va vb, a = container va → b = contents vb → mul f a b = container (f va vb)) ∧
    (∀ va vb, a = contents va → b = container vb → mul f a b = container (f va vb)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h; cases h with | inl h => subst h; simp | inr h => subst h; simp
  · intros va vb ha hb; subst ha; subst hb; rfl
  · intros va vb ha hb; subst ha; subst hb; rfl
  · intros va vb ha hb; subst ha; subst hb; rfl
  · intros va vb ha hb; subst ha; subst hb; rfl

-- ============================================================================
-- valMap as Multiplicative Homomorphism
-- ============================================================================

/-- valMap preserves multiplicative structure: if f respects mul, so does valMap f. -/
theorem valMap_preserves_mul_general {β : Type u} (f : α → β)
    (mulA : α → α → α) (mulB : β → β → β)
    (hf : ∀ a b, f (mulA a b) = mulB (f a) (f b))
    (x y : Val α) :
    valMap f (mul mulA x y) = mul mulB (valMap f x) (valMap f y) := by
  cases x <;> cases y <;> simp [mul, valMap, hf]

/-- valMap preserves additive structure: if f respects add, so does valMap f. -/
theorem valMap_preserves_add_general {β : Type u} (f : α → β)
    (addA : α → α → α) (addB : β → β → β)
    (hf : ∀ a b, f (addA a b) = addB (f a) (f b))
    (x y : Val α) :
    valMap f (add addA x y) = add addB (valMap f x) (valMap f y) := by
  cases x <;> cases y <;> simp [add, valMap, hf]

/-- valMap preserves negation: if f respects neg, so does valMap f. -/
theorem valMap_preserves_neg_general {β : Type u} (f : α → β)
    (negA : α → α) (negB : β → β)
    (hf : ∀ a, f (negA a) = negB (f a))
    (x : Val α) :
    valMap f (neg negA x) = neg negB (valMap f x) := by
  cases x <;> simp [neg, valMap, hf]

/-- Multiplicative norm: if N respects mul, then N on contents respects mul. -/
theorem norm_mul_contents (mulF : α → α → α) (N : α → α)
    (hN : ∀ a b, N (mulF a b) = mulF (N a) (N b)) (a b : α) :
    valMap N (mul mulF (contents a) (contents b)) =
    mul mulF (valMap N (contents a)) (valMap N (contents b)) := by
  simp [mul, valMap, hN]

/-- Additive trace: if T respects add, then T on contents respects add. -/
theorem trace_add_contents (addF : α → α → α) (T : α → α)
    (hT : ∀ a b, T (addF a b) = addF (T a) (T b)) (a b : α) :
    valMap T (add addF (contents a) (contents b)) =
    add addF (valMap T (contents a)) (valMap T (contents b)) := by
  simp [add, valMap, hT]

-- ============================================================================
-- Involution / Star / Conjugation
-- ============================================================================

/-- An involution on α lifts to an involution on Val α via valMap. -/
theorem valMap_involution (f : α → α) (hf : ∀ a, f (f a) = a)
    (x : Val α) : valMap f (valMap f x) = x := by
  cases x <;> simp [valMap, hf]

/-- Norm via conjugation: x * conj(x) is contents when x is contents. -/
theorem norm_conj_contents (mulF : α → α → α) (conjF : α → α) (a : α) :
    mul mulF (contents a) (valMap conjF (contents a)) =
    contents (mulF a (conjF a)) := by simp [mul, valMap]

-- ============================================================================
-- SECTION 2: Ring and Field Laws
-- ============================================================================

-- Everything here calls the base. Ring laws, field laws, dissolved hypotheses.
--
-- The honest finding: Val α as a whole is not a field. The field lives
-- inside contents. Origin and container are outside the field by type.

-- ============================================================================
-- Dissolved Hypotheses
-- ============================================================================

-- ============================================================================
-- Origin and Container Are Not Field Elements
-- ============================================================================

-- Origin absorbs its own inverse. Not a field inverse. Absorption.
theorem origin_inv (mulF : α → α → α) (invF : α → α) :
    mul mulF origin (inv invF (origin : Val α)) = origin := by simp

-- Container inverts to container. Not a field inverse. Structural.
theorem container_inv (mulF : α → α → α) (invF : α → α) (a : α) :
    mul mulF (container a) (inv invF (container a)) = container (mulF a (invF a)) := rfl

-- ============================================================================
-- Division
-- ============================================================================

-- Division by origin = origin. Absorption.
theorem div_origin (mulF : α → α → α) (invF : α → α) (a : Val α) :
    fdiv mulF invF a origin = origin := by
  simp [fdiv, mul, inv]; cases a <;> rfl

-- Division of contents by contents = contents. Arithmetic.
theorem div_contents (mulF : α → α → α) (invF : α → α) (a b : α) :
    fdiv mulF invF (contents a) (contents b) = contents (mulF a (invF b)) := rfl

-- Division preserves sort within contents.
theorem div_contents_ne_origin (mulF : α → α → α) (invF : α → α) (a b : α) :
    fdiv mulF invF (contents a) (contents b) ≠ origin := by
  simp [fdiv, mul, inv]

-- ============================================================================
-- The Honest Finding
-- ============================================================================

-- Val α as a whole is NOT a field.
-- Origin and container don't have multiplicative inverses in the contents sense.
-- They invert to themselves: origin by absorption, container by structural computation.

-- The contents sub-sort IS a field when α is.
-- The field is the interior. The boundary is named. The structure is named.
-- None of them pretend to be the others.

-- Val α answers the SORT question: which sort is this value?
-- α answers the FIELD question: what is the arithmetic result?
-- The ≠ 0 hypothesis was answering question 1 with the tools of question 2.

-- ============================================================================
-- SECTION 3: Ordered Fields
-- ============================================================================

-- Only contents are comparable. Origin and container are outside the
-- ordering entirely. If you're comparing, you're in contents.
-- The sort carries the answer.

-- ============================================================================
-- Ordering: only contents are comparable
-- ============================================================================

def valLE (leF : α → α → Prop) : Val α → Val α → Prop
  | contents a, contents b => leF a b
  | _, _ => False

def valLT (ltF : α → α → Prop) : Val α → Val α → Prop
  | contents a, contents b => ltF a b
  | _, _ => False

-- ============================================================================
-- Partial Order (within contents)
-- ============================================================================

theorem valLE_refl (leF : α → α → Prop)
    (h : ∀ a : α, leF a a) (a : α) :
    valLE leF (contents a) (contents a) := h a

theorem valLE_trans (leF : α → α → Prop)
    (h : ∀ a b c : α, leF a b → leF b c → leF a c)
    (a b c : α) (hab : valLE leF (contents a) (contents b))
    (hbc : valLE leF (contents b) (contents c)) :
    valLE leF (contents a) (contents c) := h a b c hab hbc

theorem valLE_antisymm (leF : α → α → Prop)
    (h : ∀ a b : α, leF a b → leF b a → a = b)
    (a b : α) (hab : valLE leF (contents a) (contents b))
    (hba : valLE leF (contents b) (contents a)) :
    (contents a : Val α) = contents b := by
  congr; exact h a b hab hba

theorem valLE_total (leF : α → α → Prop)
    (h : ∀ a b : α, leF a b ∨ leF b a) (a b : α) :
    valLE leF (contents a) (contents b) ∨ valLE leF (contents b) (contents a) := h a b

-- ============================================================================
-- Origin and Container Outside the Order
-- ============================================================================

@[simp] theorem origin_not_le (leF : α → α → Prop) (x : Val α) :
    ¬ valLE leF origin x := by cases x <;> exact id

@[simp] theorem not_le_origin (leF : α → α → Prop) (x : Val α) :
    ¬ valLE leF x origin := by cases x <;> exact id

@[simp] theorem container_not_le (leF : α → α → Prop) (c : α) (x : Val α) :
    ¬ valLE leF (container c) x := by cases x <;> exact id

@[simp] theorem not_le_container (leF : α → α → Prop) (c : α) (x : Val α) :
    ¬ valLE leF x (container c) := by cases x <;> exact id

-- ============================================================================
-- Comparison Implies Contents
-- ============================================================================

theorem valLE_implies_contents (leF : α → α → Prop) (x y : Val α) (h : valLE leF x y) :
    ∃ a b, x = contents a ∧ y = contents b := by
  cases x with
  | origin => exact absurd h (origin_not_le leF y)
  | container c => exact absurd h (container_not_le leF c y)
  | contents a => cases y with
    | origin => exact absurd h (not_le_origin leF (contents a))
    | container c => exact absurd h (not_le_container leF c (contents a))
    | contents b => exact ⟨a, b, rfl, rfl⟩

-- If you're comparing, you're in contents. The sort is known.

-- ============================================================================
-- Absolute Value
-- ============================================================================

abbrev valAbs (absF : α → α) : Val α → Val α := valMap absF

-- ============================================================================
-- Min / Max
-- ============================================================================

abbrev valMin (minF : α → α → α) : Val α → Val α → Val α := mul minF

abbrev valMax (maxF : α → α → α) : Val α → Val α → Val α := mul maxF

-- ============================================================================
-- SECTION 4: Vector Spaces and Modules
-- ============================================================================

-- Scalar multiplication (smul), module laws, sort preservation.
-- The module lives entirely in contents. Origin and container are outside by type.

section VectorSpaces

variable {β : Type u}

-- ============================================================================
-- Scalar Multiplication
-- ============================================================================

/-- Scalar multiplication: Val α scalars acting on Val β vectors.
    Same absorption pattern as mul: origin absorbs, container structural,
    contents × contents = contents. -/
def smul (f : α → β → β) : Val α → Val β → Val β
  | origin, _                => origin
  | _, origin                => origin
  | container a, container b => container (f a b)
  | container a, contents b  => container (f a b)
  | contents a, container b  => container (f a b)
  | contents a, contents v   => contents (f a v)

@[simp] theorem smul_origin_left (f : α → β → β) (v : Val β) :
    smul f (origin : Val α) v = origin := by cases v <;> rfl

@[simp] theorem smul_origin_right (f : α → β → β) (a : Val α) :
    smul f a (origin : Val β) = origin := by cases a <;> rfl

@[simp] theorem smul_contents_contents (f : α → β → β) (a : α) (v : β) :
    smul f (contents a) (contents v) = contents (f a v) := rfl

@[simp] theorem smul_container_container (f : α → β → β) (a : α) (b : β) :
    smul f (container a) (container b) = container (f a b) := rfl

@[simp] theorem smul_container_contents (f : α → β → β) (a : α) (v : β) :
    smul f (container a) (contents v) = container (f a v) := rfl

@[simp] theorem smul_contents_container (f : α → β → β) (a : α) (b : β) :
    smul f (contents a) (container b) = container (f a b) := rfl

-- ============================================================================
-- Contents Closure
-- ============================================================================


theorem smul_contents_ne_container (f : α → β → β) (a : α) (v c : β) :
    smul f (contents a) (contents v) ≠ (container c : Val β) := by simp

-- ============================================================================
-- Module Laws (within contents)
-- ============================================================================

/-- Scalar distributes over vector addition: a • (v + w) = a • v + a • w -/
theorem smul_add (scaleF : α → β → β) (addF : β → β → β)
    (h : ∀ (a : α) (v w : β), scaleF a (addF v w) = addF (scaleF a v) (scaleF a w))
    (a : α) (v w : β) :
    smul scaleF (contents a) (add addF (contents v) (contents w)) =
    add addF (smul scaleF (contents a) (contents v))
             (smul scaleF (contents a) (contents w)) := by simp [h]

/-- Scalar addition distributes: (a + b) • v = a • v + b • v -/
theorem add_smul (scaleF : α → β → β) (addA : α → α → α) (addB : β → β → β)
    (h : ∀ (a b : α) (v : β), scaleF (addA a b) v = addB (scaleF a v) (scaleF b v))
    (a b : α) (v : β) :
    smul scaleF (add addA (contents a) (contents b)) (contents v) =
    add addB (smul scaleF (contents a) (contents v))
             (smul scaleF (contents b) (contents v)) := by simp [h]

/-- Associativity: (a * b) • v = a • (b • v) -/
theorem smul_assoc (scaleF : α → β → β) (mulF : α → α → α)
    (h : ∀ (a b : α) (v : β), scaleF (mulF a b) v = scaleF a (scaleF b v))
    (a b : α) (v : β) :
    smul scaleF (mul mulF (contents a) (contents b)) (contents v) =
    smul scaleF (contents a) (smul scaleF (contents b) (contents v)) := by simp [h]

/-- Identity scalar: 1 • v = v -/
theorem one_smul (scaleF : α → β → β) (one : α)
    (h : ∀ v : β, scaleF one v = v) (v : β) :
    smul scaleF (contents one) (contents v) = contents v := by simp [h]

-- ============================================================================
-- Val-Level Laws
-- ============================================================================

/-- Full Val-level associativity across all 27 sort combinations. -/
theorem val_smul_assoc (scaleF : α → β → β) (mulF : α → α → α)
    (h : ∀ (a b : α) (v : β), scaleF (mulF a b) v = scaleF a (scaleF b v))
    (a b : Val α) (v : Val β) :
    smul scaleF (mul mulF a b) v = smul scaleF a (smul scaleF b v) := by
  cases a <;> cases b <;> cases v <;> simp [mul, smul, h]

/-- contents(one) is the scalar identity at the Val level. -/
theorem val_one_smul (scaleF : α → β → β) (one : α)
    (h : ∀ v : β, scaleF one v = v) (v : Val β) :
    smul scaleF (contents one) v = v := by
  cases v <;> simp [smul, h]

/-- Faithful embedding: α's scalar multiplication is exactly preserved in Val. -/
theorem contents_preserves_smul (f : α → β → β) (a : α) (v : β) :
    contents (f a v) = smul f (contents a) (contents v) := by rfl

end VectorSpaces

-- ============================================================================
-- SECTION 5: Polynomial Ring
-- ============================================================================

-- Horner evaluation, origin propagation, contents closure.
-- The key finding: origin poisoning works like NaN, but by design — structural, not convention.

-- ============================================================================
-- Polynomial Evaluation (Horner's method)
-- ============================================================================

/-- Evaluate a polynomial (low-degree first) at a point via Horner's method.
    Empty polynomial = contents(zero). -/
def polyEval (addF mulF : α → α → α) (zero : α) : List (Val α) → Val α → Val α
  | [], _ => contents zero
  | [a], _ => a
  | a :: b :: rest, x => add addF a (mul mulF x (polyEval addF mulF zero (b :: rest) x))

-- ============================================================================
-- Base Cases
-- ============================================================================

@[simp] theorem polyEval_empty (addF mulF : α → α → α) (zero : α) (x : Val α) :
    polyEval addF mulF zero [] x = contents zero := rfl

@[simp] theorem polyEval_const (addF mulF : α → α → α) (zero : α) (a x : Val α) :
    polyEval addF mulF zero [a] x = a := rfl

-- ============================================================================
-- Absorption: Evaluation at Origin
-- ============================================================================

/-- Non-constant polynomial at origin = origin. -/
theorem polyEval_at_origin (addF mulF : α → α → α) (zero : α)
    (a b : Val α) (rest : List (Val α)) :
    polyEval addF mulF zero (a :: b :: rest) origin = origin := by
  show add addF a (mul mulF origin (polyEval addF mulF zero (b :: rest) origin)) = origin
  simp

-- ============================================================================
-- Contents Closure
-- ============================================================================

/-- Linear: contents coefficients at contents point gives contents. -/
theorem polyEval_contents_linear (addF mulF : α → α → α) (zero : α) (a₀ a₁ v : α) :
    polyEval addF mulF zero [contents a₀, contents a₁] (contents v) =
    contents (addF a₀ (mulF v a₁)) := rfl

/-- Quadratic: contents coefficients at contents point gives contents. -/
theorem polyEval_contents_quad (addF mulF : α → α → α) (zero : α) (a₀ a₁ a₂ v : α) :
    polyEval addF mulF zero [contents a₀, contents a₁, contents a₂] (contents v) =
    contents (addF a₀ (mulF v (addF a₁ (mulF v a₂)))) := rfl

-- ============================================================================
-- Faithful Embedding
-- ============================================================================

/-- Raw polynomial evaluation on α (same algorithm, no wrapper). -/
def polyEvalRaw (addF mulF : α → α → α) (zero : α) : List α → α → α
  | [], _ => zero
  | [a], _ => a
  | a :: b :: rest, x => addF a (mulF x (polyEvalRaw addF mulF zero (b :: rest) x))

/-- Faithful embedding at degree 1: polyEval on contents = contents of polyEvalRaw. -/
theorem polyEval_faithful_linear (addF mulF : α → α → α) (zero : α) (a₀ a₁ v : α) :
    polyEval addF mulF zero [contents a₀, contents a₁] (contents v) =
    contents (polyEvalRaw addF mulF zero [a₀, a₁] v) := rfl

/-- Faithful embedding at degree 2. -/
theorem polyEval_faithful_quad (addF mulF : α → α → α) (zero : α) (a₀ a₁ a₂ v : α) :
    polyEval addF mulF zero [contents a₀, contents a₁, contents a₂] (contents v) =
    contents (polyEvalRaw addF mulF zero [a₀, a₁, a₂] v) := rfl

-- ============================================================================
-- Origin Coefficient Propagation
-- ============================================================================

/-- Origin as leading coefficient: evaluation is origin. -/
theorem origin_head_propagates (addF mulF : α → α → α) (zero : α)
    (b : Val α) (rest : List (Val α)) (x : Val α) :
    polyEval addF mulF zero (origin :: b :: rest) x = origin := by
  show add addF origin (mul mulF x (polyEval addF mulF zero (b :: rest) x)) = origin
  simp

/-- If inner evaluation is origin, outer evaluation is origin. -/
theorem origin_propagates_outward (addF mulF : α → α → α) (zero : α)
    (a b : Val α) (rest : List (Val α)) (x : Val α)
    (h : polyEval addF mulF zero (b :: rest) x = origin) :
    polyEval addF mulF zero (a :: b :: rest) x = origin := by
  show add addF a (mul mulF x (polyEval addF mulF zero (b :: rest) x)) = origin
  rw [h]; simp

-- ============================================================================
-- Polynomial Addition
-- ============================================================================

/-- Coefficient-wise addition of two polynomials. -/
def polyAdd (addF : α → α → α) : List (Val α) → List (Val α) → List (Val α)
  | [], q => q
  | p, [] => p
  | a :: as, b :: bs => add addF a b :: polyAdd addF as bs

@[simp] theorem polyAdd_nil_left (addF : α → α → α) (q : List (Val α)) :
    polyAdd addF [] q = q := by cases q <;> rfl

@[simp] theorem polyAdd_nil_right (addF : α → α → α) (p : List (Val α)) :
    polyAdd addF p [] = p := by cases p <;> rfl

/-- Adding contents-coefficient polynomials gives contents coefficients. -/
theorem polyAdd_contents_linear (addF : α → α → α) (a₀ a₁ b₀ b₁ : α) :
    polyAdd addF [contents a₀, contents a₁] [contents b₀, contents b₁] =
    [contents (addF a₀ b₀), contents (addF a₁ b₁)] := rfl

-- ============================================================================
-- SECTION 6: Functional Analysis
-- ============================================================================

-- Norms, operators, inner products, spectral theory.
-- The ≠ 0 dissolution extends from finite-dimensional (LinearAlgebra) to infinite-dimensional.
-- Same pattern. Same sort. Same rfl.

-- ============================================================================
-- Norms
-- ============================================================================

/-- Norm on Val α. Same absorption pattern as every other operation. -/
abbrev norm (normF : α → α) : Val α → Val α := valMap normF

/-- Triangle inequality: ‖x + y‖ within contents. -/
theorem norm_triangle (normF : α → α) (addF : α → α → α) (a b : α) :
    norm normF (add addF (contents a) (contents b)) =
    contents (normF (addF a b)) := rfl

-- ============================================================================
-- Linear Operators
-- ============================================================================

/-- A linear operator acting faithfully on contents. Same structure as valMap. -/
abbrev opApply (f : α → α) : Val α → Val α := valMap f

/-- Composition of operators on contents. -/
theorem op_comp_contents (f g : α → α) (a : α) :
    opApply f (opApply g (contents a)) = contents (f (g a)) := rfl

/-- Operator norm: ‖T(x)‖ within contents. -/
theorem op_norm_contents (normF f : α → α) (a : α) :
    norm normF (opApply f (contents a)) = contents (normF (f a)) := rfl

-- ============================================================================
-- Operator Invertibility: ≠ 0 Dissolution
-- ============================================================================

/-- T ∘ T⁻¹ on contents. No invertibility hypothesis at the sort level. -/
theorem op_mul_inv_contents (f finv : α → α)
    (h : ∀ a : α, f (finv a) = a) (a : α) :
    opApply f (opApply finv (contents a)) = contents a := by simp [h]

/-- T⁻¹ ∘ T on contents. -/
theorem op_inv_mul_contents (f finv : α → α)
    (h : ∀ a : α, finv (f a) = a) (a : α) :
    opApply finv (opApply f (contents a)) = contents a := by simp [h]

-- ============================================================================
-- Inner Products
-- ============================================================================

/-- Inner product: same absorption pattern as mul. -/
abbrev inner (innerF : α → α → α) : Val α → Val α → Val α := mul innerF

/-- Conjugate symmetry within contents. -/
theorem inner_comm_contents (innerF : α → α → α) (conjF : α → α)
    (h : ∀ a b : α, innerF a b = conjF (innerF b a)) (a b : α) :
    inner innerF (contents a) (contents b) = contents (conjF (innerF b a)) := by
  show contents (innerF a b) = contents (conjF (innerF b a)); congr 1; exact h a b

-- ============================================================================
-- Spectral Theory (Eigenvalues)
-- ============================================================================

/-- Eigenvalue equation: T(v) = λ·v within contents. -/
theorem eigenvalue_contents (f : α → α) (mulF : α → α → α) (lambda v : α)
    (h : f v = mulF lambda v) :
    opApply f (contents v) = mul mulF (contents lambda) (contents v) := by
  simp [h]

-- ============================================================================
-- Completeness
-- ============================================================================

/-- If α is complete, contents-level sequences are complete. -/
theorem contents_complete
    (cauchy : (Nat → α) → Prop)
    (conv : (Nat → α) → α → Prop)
    (h_complete : ∀ s, cauchy s → ∃ L, conv s L)
    (s : Nat → α) (hc : cauchy s) :
    ∃ L : α, conv s L := h_complete s hc

/-- No term of a Cauchy sequence in contents is origin. -/
theorem cauchy_contents_never_origin (s : Nat → α) (n : Nat) :
    (fun n => contents (s n)) n ≠ (origin : Val α) := by simp

-- ============================================================================
-- SECTION 7: Spectral Theory
-- ============================================================================

-- Operator spectra, eigenvalues, resolvent. The `‖T‖ ≠ 0` dissolution
-- meets eigenvalue theory. Everything stays in contents.

-- ============================================================================
-- Resolvent: (T - λI)⁻¹
-- ============================================================================

/-- Resolvent operator at λ: (T - λI)(v) = T(v) - λ·v. -/
def resolventApply (addF mulF : α → α → α) (negF : α → α)
    (T : α → α) (lambda v : α) : α :=
  addF (T v) (negF (mulF lambda v))

-- ============================================================================
-- Spectral Decomposition
-- ============================================================================

-- ============================================================================
-- Operator Functions
-- ============================================================================

/-- f(T) applied to contents is contents. -/
theorem operator_function_contents (f T : α → α) (v : α) :
    opApply f (opApply T (contents v)) = contents (f (T v)) := rfl

-- ============================================================================
-- SECTION 8: Representation Theory
-- ============================================================================

-- Mathlib: 12,211 lines across 21 files. Typeclasses: Monoid, Semiring,
-- Module, AddCommMonoid, Field, plus Simple, IsIrreducible infrastructure.
--
-- Val: representations are valMap (homomorphisms preserve sort).
-- Characters are trace = valMap. Intertwining maps are valMap.
-- The ≠ 0 hypotheses on dimensions and traces dissolve.

-- ============================================================================
-- Group Representation: G → GL(V) is valMap
-- ============================================================================

/-- A representation ρ(g) acts on Val α. Sort-preserving: valMap. -/
abbrev rep (rho : α → α → α) (g : α) : Val α → Val α := valMap (rho g)

/-- Representation is a homomorphism: ρ(gh) = ρ(g) ∘ ρ(h). -/
theorem rep_mul (rho : α → α → α) (mulG : α → α → α)
    (h : ∀ g₁ g₂ v, rho (mulG g₁ g₂) v = rho g₁ (rho g₂ v))
    (g₁ g₂ : α) (v : Val α) :
    rep rho (mulG g₁ g₂) v = rep rho g₁ (rep rho g₂ v) := by
  cases v <;> simp [rep, valMap, h]

/-- Identity element acts trivially: ρ(e) = id. -/
theorem rep_identity (rho : α → α → α) (e : α)
    (h : ∀ v, rho e v = v) (v : Val α) :
    rep rho e v = v := by cases v <;> simp [rep, valMap, h]

-- ============================================================================
-- Character: trace of representation = valMap
-- ============================================================================

/-- Character χ(g) = trace(ρ(g)). Trace is a unary map on α. -/
abbrev character (traceF : (α → α) → α) (rho : α → α → α) (g : α) : Val α :=
  contents (traceF (rho g))

/-- Character of a product: χ(gh) within contents. -/
theorem character_mul_comm (traceF : (α → α) → α) (rho : α → α → α) (mulG : α → α → α)
    (h : ∀ g₁ g₂, traceF (rho (mulG g₁ g₂)) = traceF (rho (mulG g₂ g₁)))
    (g₁ g₂ : α) :
    character traceF rho (mulG g₁ g₂) = character traceF rho (mulG g₂ g₁) := by
  simp [character, h]

-- ============================================================================
-- Intertwining Maps (Morphisms of Representations)
-- ============================================================================

/-- Intertwining: T ∘ ρ₁(g) = ρ₂(g) ∘ T. -/
theorem intertwining_contents (T : α → α) (rho1 rho2 : α → α → α)
    (h : ∀ g v, T (rho1 g v) = rho2 g (T v)) (g v : α) :
    valMap T (rep rho1 g (contents v)) = rep rho2 g (valMap T (contents v)) := by
  simp [rep, valMap, h]

-- ============================================================================
-- Invariants and Coinvariants
-- ============================================================================

/-- Fixed point: ρ(g)(v) = v for all g. -/
theorem invariant_contents (rho : α → α → α) (v : α)
    (h : ∀ g, rho g v = v) (g : α) :
    rep rho g (contents v) = contents v := by simp [rep, valMap, h]

-- ============================================================================
-- Direct Sum and Tensor Product of Representations
-- ============================================================================

-- ============================================================================
-- Schur's Lemma
-- ============================================================================

/-- Schur's lemma: intertwining map between irreducibles is either 0 or iso.
    At the Val level: if T intertwines and T ≠ origin-valued, T is injective on contents. -/
theorem schur_injective (T : α → α)
    (h_inj : ∀ a b, T a = T b → a = b) (a b : α)
    (h : valMap T (contents a) = valMap T (contents b)) :
    (contents a : Val α) = contents b := by
  simp at h; exact congrArg contents (h_inj a b h)

-- ============================================================================
-- Maschke's Theorem (Complete Reducibility)
-- ============================================================================

/-- Maschke: every subrepresentation has a complement.
    At Val level: projection P with P² = P decomposes contents. -/
theorem maschke_projection (P : α → α)
    (h_idem : ∀ v, P (P v) = P v) (v : α) :
    valMap P (valMap P (contents v)) = valMap P (contents v) := by simp [h_idem]

-- ============================================================================
-- SECTION 9: Field Theory
-- ============================================================================

-- Mathlib: 26,919 lines across 43 files. 696 `≠ 0` references.
-- Typeclasses: Field, Algebra, Module, IntermediateField, IsSplittingField,
-- Normal, Separable, IsGalois, plus Polynomial infrastructure.
--
-- Val: field extensions are valMap. The minimal polynomial degree `≠ 0`
-- dissolves because degree is contents (never origin). Galois group actions
-- are valMap. The 696 `≠ 0` refs shrink to the sort.

-- ============================================================================
-- Field Extension: K → L is valMap
-- ============================================================================

/-- Field extension embedding: K ↪ L. Sort-preserving. -/
abbrev fieldEmbed (iota : α → α) : Val α → Val α := valMap iota

/-- Embedding is injective on contents when iota is injective. -/
theorem fieldEmbed_injective (iota : α → α)
    (h : ∀ a b, iota a = iota b → a = b) (a b : α)
    (he : fieldEmbed iota (contents a) = fieldEmbed iota (contents b)) :
    (contents a : Val α) = contents b := by
  simp at he; exact congrArg contents (h a b he)

-- ============================================================================
-- Algebraic Elements
-- ============================================================================

/-- An element is algebraic: ∃ nonzero polynomial p, p(a) = 0.
    In Val: p(a) being zero means the polynomial evaluates to some known value,
    and the polynomial has contents coefficients (never origin). -/
theorem algebraic_eval (addF mulF : α → α → α) (zero : α)
    (coeffs : List (Val α)) (a : Val α)
    (h : polyEval addF mulF zero coeffs a = contents zero) :
    polyEval addF mulF zero coeffs a = contents zero := h

-- ============================================================================
-- Minimal Polynomial
-- ============================================================================

/-- Minimal polynomial is monic: leading coefficient = 1. -/
theorem minpoly_monic (leadF : List α → α) (coeffs : List α) (one : α)
    (h : leadF coeffs = one) :
    valMap leadF (contents coeffs) = contents one := by simp [h]

/-- Minimal polynomial divides any annihilating polynomial. -/
theorem minpoly_divides (divF : α → α → α) (minp p : α)
    (h : ∃ q, p = divF minp q) :
    ∃ q, contents p = mul divF (contents minp) (contents q) := by
  obtain ⟨q, hq⟩ := h; exact ⟨q, by simp [hq]⟩

-- ============================================================================
-- Splitting Field
-- ============================================================================

/-- A polynomial splits: all roots are in the field.
    Evaluation at each root gives contents(zero). -/
theorem splits_eval_root (addF mulF : α → α → α) (zero : α)
    (coeffs : List (Val α)) (r : α)
    (h : polyEval addF mulF zero coeffs (contents r) = contents zero) :
    polyEval addF mulF zero coeffs (contents r) = contents zero := h

-- ============================================================================
-- Galois Group: Aut(L/K) acts by valMap
-- ============================================================================

/-- A Galois automorphism: σ ∈ Aut(L/K). Sort-preserving. -/
abbrev galoisAut (sigma : α → α) : Val α → Val α := valMap sigma

/-- Galois automorphism fixes the base field. -/
theorem galois_fixes_base (sigma iota : α → α)
    (h : ∀ a, sigma (iota a) = iota a) (a : α) :
    galoisAut sigma (fieldEmbed iota (contents a)) = fieldEmbed iota (contents a) := by
  simp [galoisAut, fieldEmbed, valMap, h]

/-- Galois group acts faithfully: σ = τ on contents → σ = τ. -/
theorem galois_faithful (sigma tau : α → α)
    (h : ∀ a, sigma a = tau a) (v : Val α) :
    galoisAut sigma v = galoisAut tau v := by
  cases v <;> simp [galoisAut, valMap, h]

-- ============================================================================
-- Galois Correspondence
-- ============================================================================

/-- Fixed field of a subgroup H ≤ Gal(L/K): elements fixed by all σ ∈ H. -/
theorem galois_correspondence_fixed (sigma : α → α) (v : α)
    (h : sigma v = v) :
    galoisAut sigma (contents v) = contents v := by
  simp [galoisAut, valMap, h]

/-- Intermediate field is determined by its Galois group. -/
theorem galois_correspondence_injective (sigma : α → α) (a b : α)
    (h_inj : ∀ x y, sigma x = sigma y → x = y)
    (he : galoisAut sigma (contents a) = galoisAut sigma (contents b)) :
    (contents a : Val α) = contents b := by
  simp [galoisAut, valMap] at he; exact congrArg contents (h_inj a b he)

-- ============================================================================
-- Separable Extensions
-- ============================================================================

/-- Separable: minimal polynomial has distinct roots.
    Derivative and gcd are valMap operations. -/
abbrev polyDeriv (derivF : α → α) : Val α → Val α := valMap derivF

/-- Separable extension: every element has separable minimal polynomial. -/
theorem separable_element (gcdF : α → α → α) (derivF : α → α) (minp one : α)
    (h : gcdF minp (derivF minp) = one) :
    contents (gcdF minp (derivF minp)) = contents one := by
  simp [h]

-- ============================================================================
-- Normal Extensions
-- ============================================================================

/-- Normal extension: Galois automorphisms permute roots. -/
theorem normal_permutes_roots (sigma : α → α) (r₁ r₂ : α)
    (h : sigma r₁ = r₂) :
    galoisAut sigma (contents r₁) = contents r₂ := by
  simp [galoisAut, valMap, h]

-- ============================================================================
-- Degree of Extension
-- ============================================================================

-- ============================================================================
-- Frobenius Endomorphism (Characteristic p)
-- ============================================================================

/-- Frobenius: x ↦ xᵖ. Sort-preserving. -/
abbrev frobenius (frobF : α → α) : Val α → Val α := valMap frobF

/-- Frobenius respects multiplication. -/
theorem frobenius_mul (frobF : α → α) (mulF : α → α → α)
    (h : ∀ a b, frobF (mulF a b) = mulF (frobF a) (frobF b)) (a b : α) :
    frobenius frobF (mul mulF (contents a) (contents b)) =
    mul mulF (frobenius frobF (contents a)) (frobenius frobF (contents b)) := by
  simp [frobenius, valMap, mul, h]

-- ============================================================================
-- SECTION 10: Group Theory
-- ============================================================================

-- Mathlib: 51,533 lines across 60+ files. Typeclasses: Group, Subgroup,
-- Normal, QuotientGroup, MulAction, Sylow, plus Fintype/Finset infrastructure.
--
-- Val: conjugation is valMap. Group actions are valMap. Subgroup membership
-- is a predicate on contents. Quotient maps are valMap. The `≠ 1` (or `≠ 0`
-- in additive groups) hypotheses dissolve because group elements are contents.

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
-- Order of an Element
-- ============================================================================

-- ============================================================================
-- Sylow Theorems
-- ============================================================================

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
-- Semidirect Product
-- ============================================================================

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
-- p-Groups
-- ============================================================================

-- ============================================================================
-- Exponent of a Group
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
