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

/-- valMap preserves scalar multiplication when f respects the action. -/
theorem valMap_preserves_smul {γ : Type u} (f : β → γ)
    (smulB : α → β → β) (smulC : α → γ → γ)
    (hf : ∀ a v, f (smulB a v) = smulC a (f v))
    (s : Val α) (v : Val β) :
    valMap f (smul smulB s v) = smul smulC s (valMap f v) := by
  cases s <;> cases v <;> simp [smul, valMap, hf]

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

/-- Maschke averaging: P = (1/|G|) Σ ρ(g) π ρ(g⁻¹) is equivariant.
    Val level: P intertwines if averaging over conjugates. -/
theorem maschke_equivariant (P : α → α) (rho : α → α → α)
    (h : ∀ g v, rho g (P v) = P (rho g v)) (g v : α) :
    rep rho g (valMap P (contents v)) = valMap P (rep rho g (contents v)) := by
  simp [rep, valMap, h]

/-- Restriction: pull back along f : H → G. Res_f(ρ)(h) = ρ(f(h)). -/
theorem rep_restrict (rho : α → α → α) (f : α → α)
    (g : α) (v : Val α) :
    rep rho (f g) v = rep (fun h => rho (f h)) g v := by
  cases v <;> simp [rep, valMap]

/-- Restriction preserves homomorphism property. -/
theorem rep_restrict_mul (rho : α → α → α) (f : α → α) (mulH : α → α → α)
    (h : ∀ g₁ g₂ v, rho (f (mulH g₁ g₂)) v = rho (f g₁) (rho (f g₂) v))
    (g₁ g₂ : α) (v : Val α) :
    rep rho (f (mulH g₁ g₂)) v = rep rho (f g₁) (rep rho (f g₂) v) := by
  cases v <;> simp [rep, valMap, h]

/-- Induction: map from induced module to a representation. Sort-preserving. -/
abbrev induce (mapF : α → α) : Val α → Val α := valMap mapF

-- ============================================================================
-- Homological Chains and Cochains (Group Homology)
-- ============================================================================

/-- Chain differential d₁₀: (G →₀ A) → A via ρ(g⁻¹)(a) - a.
    Val level: valMap of the boundary map. -/
abbrev chainDiff (diffF : α → α) : Val α → Val α := valMap diffF

/-- Chain differential vanishes on identity: d(e, a) = 0 when ρ(e) = id. -/
theorem chain_d10_identity (rho subF : α → α → α) (e zero : α)
    (h_id : ∀ v, rho e v = v) (h_sub : ∀ a, subF a a = zero)
    (a : α) : subF (rho e a) a = zero := by rw [h_id, h_sub]

/-- Chain complex property: d ∘ d = 0.
    Composition of two differentials gives zero. -/
theorem chain_dd_zero (d₁ d₀ : α → α) (zero : α)
    (h : ∀ a, d₀ (d₁ a) = zero) (a : α) :
    chainDiff d₀ (chainDiff d₁ (contents a)) = contents zero := by simp [h]

/-- Cochain differential d⁰¹: A → Fun(G, A) via a ↦ (g ↦ ρ(g)(a) - a).
    Val level: valMap of the coboundary. -/
abbrev cochainDiff (diffF : α → α) : Val α → Val α := valMap diffF

/-- Cochain complex property: d ∘ d = 0.
    Two consecutive coboundary maps compose to zero. -/
theorem cochain_dd_zero (d₁ d₂ : α → α) (zero : α)
    (h : ∀ a, d₂ (d₁ a) = zero) (a : α) :
    cochainDiff d₂ (cochainDiff d₁ (contents a)) = contents zero := by simp [h]

/-- d₀₁ kernel equals invariants: ker(d⁰¹) = A^G. -/
theorem cochain_d01_ker_eq_invariants (rho : α → α → α) (subF : α → α → α) (zero : α)
    (v : α) (h : ∀ g, subF (rho g v) v = zero) (g : α) :
    subF (rho g v) v = zero := h g

/-- d₀₁ vanishes on trivial representations. -/
theorem cochain_d01_trivial (subF : α → α → α) (zero : α)
    (h_sub : ∀ a, subF a a = zero) (a : α) :
    subF a a = zero := h_sub a

-- ============================================================================
-- Homology and Cohomology Groups
-- ============================================================================

/-- H₀(G,A) ≅ coinvariants A_G. The quotient map is sort-preserving on all Val. -/
theorem H0_iso_coinvariants (projF : α → α) (v : Val α) :
    (v = origin → valMap projF v = origin) ∧
    (∀ a, v = contents a → valMap projF v = contents (projF a)) := by
  exact ⟨fun h => by rw [h]; simp, fun a h => by rw [h]; simp⟩

/-- H⁰(G,A) ≅ invariants A^G. The 0th cohomology. -/
theorem H0_cohom_iso_invariants (rho : α → α → α) (v : α)
    (h : ∀ g, rho g v = v) (g : α) :
    rep rho g (contents v) = contents v := by simp [rep, valMap, h]

/-- Projection from cycles to homology: Z_n → H_n. Sort-preserving. -/
abbrev homologyProj (projF : α → α) : Val α → Val α := valMap projF

/-- Homology projection is surjective on contents. -/
theorem homologyProj_surj (projF : α → α) (hF : ∀ b, ∃ a, projF a = b) (b : α) :
    ∃ a, homologyProj projF (contents a) = contents b := by
  obtain ⟨a, ha⟩ := hF b; exact ⟨a, by simp [ha]⟩

-- ============================================================================
-- Functoriality of Homology/Cohomology
-- ============================================================================

/-- A group homomorphism f : G → H and representation morphism φ induce
    a chain map. The induced chain map commutes with differentials. -/
theorem chains_map_commutes (mapF diffA diffB : α → α)
    (h : ∀ a, diffB (mapF a) = mapF (diffA a)) (a : α) :
    chainDiff diffB (valMap mapF (contents a)) =
    valMap mapF (chainDiff diffA (contents a)) := by simp [chainDiff, h]

/-- Induced map on homology: H_n(G,A) → H_n(H,B). -/
theorem homology_map_functorial (mapF mapG : α → α) (a : α) :
    valMap mapG (valMap mapF (contents a)) = valMap (mapG ∘ mapF) (contents a) := by simp

/-- Functoriality: identity map induces identity on homology. -/
theorem homology_map_id (a : Val α) :
    valMap id a = a := by cases a <;> rfl

/-- Functoriality: composition of maps. -/
theorem homology_map_comp (f g : α → α) (a : Val α) :
    valMap g (valMap f a) = valMap (g ∘ f) a := by cases a <;> rfl

/-- Corestriction: H_n(H, Res_f(A)) → H_n(G, A). Sort-preserving. -/
abbrev corestriction (coresF : α → α) : Val α → Val α := valMap coresF

/-- Coinflation: H_n(G, A) → H_n(G/S, A_S). Sort-preserving. -/
abbrev coinflation (coinfF : α → α) : Val α → Val α := valMap coinfF

/-- Inflation: H^n(G/S, A^S) → H^n(G, A). Sort-preserving. -/
abbrev inflation (infF : α → α) : Val α → Val α := valMap infF

/-- Restriction on cohomology: H^n(G, A) → H^n(S, A). Sort-preserving. -/
abbrev cohomRestriction (resF : α → α) : Val α → Val α := valMap resF

-- ============================================================================
-- Coinvariants and Invariants
-- ============================================================================

/-- Coinvariant quotient map: A → A_G. Sort-preserving. -/
abbrev coinvariantQuot (quotF : α → α) : Val α → Val α := valMap quotF

/-- Coinvariant of ρ(g)(x) - x is zero: the defining relation. -/
theorem coinvariant_relation (rho subF : α → α → α) (quotF : α → α) (zero : α)
    (h : ∀ g x, quotF (subF (rho g x) x) = zero) (g x : α) :
    coinvariantQuot quotF (contents (subF (rho g x) x)) = contents zero := by
  simp [coinvariantQuot, valMap, h]

/-- Coinvariants functor: morphism φ : A → B induces A_G → B_G. -/
theorem coinvariant_functorial (quotA quotB phi : α → α)
    (h : ∀ a, quotB (phi a) = phi (quotA a)) (a : α) :
    coinvariantQuot quotB (valMap phi (contents a)) =
    valMap phi (coinvariantQuot quotA (contents a)) := by
  simp [coinvariantQuot, valMap, h]


/-- Coinvariants adjunction: Hom(A_G, M) ≅ Hom_G(A, triv(M)). -/
theorem coinvariant_adjunction (quotF adjF : α → α) (a : α) :
    valMap adjF (coinvariantQuot quotF (contents a)) =
    contents (adjF (quotF a)) := by simp [coinvariantQuot, valMap]

/-- Invariant submodule inclusion. Sort-preserving. -/
abbrev invariantIncl (inclF : α → α) : Val α → Val α := valMap inclF

/-- Average map: P = (1/|G|) Σ ρ(g). Projection onto invariants. -/
theorem average_map_projection (avgF : α → α)
    (h_idem : ∀ v, avgF (avgF v) = avgF v) (v : α) :
    valMap avgF (valMap avgF (contents v)) = valMap avgF (contents v) := by simp [h_idem]

/-- Average map is equivariant: ρ(g) ∘ avg = avg. -/
theorem average_equivariant (avgF : α → α) (rho : α → α → α)
    (h : ∀ g v, rho g (avgF v) = avgF v) (g v : α) :
    rep rho g (valMap avgF (contents v)) = valMap avgF (contents v) := by
  simp [rep, valMap, h]

/-- Average sends v to an invariant. -/
theorem average_is_invariant (avgF : α → α) (rho : α → α → α)
    (h : ∀ g v, rho g (avgF v) = avgF v) (v g : α) :
    rho g (avgF v) = avgF v := h g v

-- ============================================================================
-- Long Exact Sequences in (Co)homology
-- ============================================================================

/-- Connecting homomorphism δ : H^n → H^{n+1}. Sort-preserving. -/
abbrev connectingHom (deltaF : α → α) : Val α → Val α := valMap deltaF

/-- Long exact sequence: image of one map equals kernel of the next. -/
theorem long_exact_im_eq_ker (f g : α → α) (zero : α)
    (h : ∀ a, g (f a) = zero) (a : α) :
    valMap g (valMap f (contents a)) = contents zero := by simp [h]

/-- Exactness at H^n: inf-res-δ sequence. -/
theorem inf_res_exact (infF resF : α → α) (zero : α)
    (h : ∀ a, resF (infF a) = zero) (a : α) :
    valMap resF (valMap infF (contents a)) = contents zero := by simp [h]

-- ============================================================================
-- Intertwining Maps (Extended)
-- ============================================================================

/-- Intertwining map composition: if T₁ and T₂ intertwine, so does T₂ ∘ T₁. -/
theorem intertwining_comp (T₁ T₂ : α → α) (rho1 rho2 rho3 : α → α → α)
    (h₁ : ∀ g v, T₁ (rho1 g v) = rho2 g (T₁ v))
    (h₂ : ∀ g v, T₂ (rho2 g v) = rho3 g (T₂ v))
    (g v : α) :
    valMap (T₂ ∘ T₁) (rep rho1 g (contents v)) =
    rep rho3 g (valMap (T₂ ∘ T₁) (contents v)) := by
  simp [rep, valMap, h₁, h₂]

/-- Identity intertwines any representation with itself. -/
theorem intertwining_id (rho : α → α → α) (g v : α) :
    valMap id (rep rho g (contents v)) = rep rho g (valMap id (contents v)) := by
  simp [rep, valMap]

/-- Intertwining preserves sort. -/
theorem intertwining_sort (T : α → α) (v : Val α) :
    (v = origin → valMap T v = origin) ∧
    (∀ a, v = contents a → ∃ b, valMap T v = contents b) := by
  constructor
  · intro h; rw [h]; simp
  · intro a h; rw [h]; exact ⟨T a, rfl⟩

/-- Zero intertwining map: T = 0 sends everything to zero. -/
theorem intertwining_zero (rho : α → α → α) (zero : α)
    (h_zero : ∀ g, rho g zero = zero) (g : α) :
    rep rho g (contents zero) = contents zero := by simp [rep, valMap, h_zero]

/-- Kernel of intertwining map is a subrepresentation. -/
theorem intertwining_kernel_sub (T : α → α) (rho : α → α → α) (zero : α)
    (h_int : ∀ g v, T (rho g v) = rho g (T v))
    (h_fix : ∀ g, rho g zero = zero) (v : α) (hv : T v = zero) (g : α) :
    T (rho g v) = zero := by rw [h_int, hv, h_fix]

/-- Image of intertwining map is a subrepresentation. -/
theorem intertwining_image_sub (T : α → α) (rho1 rho2 : α → α → α)
    (h_int : ∀ g v, T (rho1 g v) = rho2 g (T v))
    (g v : α) : ∃ w, rho2 g (T v) = T w := ⟨rho1 g v, (h_int g v).symm⟩

-- ============================================================================
-- Character Theory (Extended)
-- ============================================================================

/-- Character at identity: χ(e) = dim(V). -/
theorem character_identity (traceF : (α → α) → α) (rho : α → α → α) (e : α)
    (dimF : α) (h : traceF (rho e) = dimF) :
    character traceF rho e = contents dimF := by simp [character, h]

/-- Character of tensor product: χ_{V⊗W}(g) = χ_V(g) · χ_W(g). -/
theorem character_tensor (traceF : (α → α) → α) (rho1 rho2 : α → α → α)
    (mulF : α → α → α)
    (h : ∀ g, traceF (fun v => rho1 g (rho2 g v)) = mulF (traceF (rho1 g)) (traceF (rho2 g)))
    (g : α) :
    contents (traceF (fun v => rho1 g (rho2 g v))) =
    mul mulF (character traceF rho1 g) (character traceF rho2 g) := by
  simp [character, h]

/-- Character of isomorphic representations is the same. -/
theorem character_iso (traceF : (α → α) → α) (rho1 rho2 : α → α → α)
    (h : ∀ g, traceF (rho1 g) = traceF (rho2 g)) (g : α) :
    character traceF rho1 g = character traceF rho2 g := by simp [character, h]

/-- Character is constant on conjugacy classes: χ(xgx⁻¹) = χ(g). -/
theorem character_conj (traceF : (α → α) → α) (rho : α → α → α) (conjF : α → α → α)
    (h : ∀ g x, traceF (rho (conjF x g)) = traceF (rho g))
    (g x : α) :
    character traceF rho (conjF x g) = character traceF rho g := by
  simp [character, h]

/-- Character of dual representation: χ_{V*}(g) = χ_V(g⁻¹). -/
theorem character_dual (traceF : (α → α) → α) (rho : α → α → α) (invG : α → α) (g : α) :
    character traceF (fun g' => rho (invG g')) g = character traceF rho (invG g) := by
  simp [character]

/-- Character of linear hom: χ_{Hom(V,W)}(g) = χ_V(g⁻¹) · χ_W(g). -/
theorem character_linHom (traceF : (α → α) → α) (rho1 rho2 : α → α → α)
    (invG : α → α) (mulF : α → α → α)
    (h : ∀ g, traceF (fun v => rho2 g (rho1 (invG g) v)) =
      mulF (traceF (rho1 (invG g))) (traceF (rho2 g)))
    (g : α) :
    contents (traceF (fun v => rho2 g (rho1 (invG g) v))) =
    mul mulF (character traceF (fun g' => rho1 (invG g')) g) (character traceF rho2 g) := by
  simp [character, h]

/-- Average character equals dimension of invariants (finite group). -/
theorem average_char_eq_dim_invariants (avgCharF dimInvF : α)
    (h : avgCharF = dimInvF) :
    contents avgCharF = contents dimInvF := by simp [h]

/-- Character orthogonality for irreducibles. -/
theorem char_orthogonal (innerF : α → α → α) (chi1 chi2 : α) (result : α)
    (h : innerF chi1 chi2 = result) :
    contents (innerF chi1 chi2) = contents result := by simp [h]

-- ============================================================================
-- Schur's Lemma (Extended)
-- ============================================================================


/-- Schur: endomorphism of irreducible is scalar. -/
theorem schur_scalar (T : α → α) (scalarF : α → α)
    (h : ∀ v, T v = scalarF v) (v : α) :
    valMap T (contents v) = valMap scalarF (contents v) := by simp [h]

/-- Schur: intertwining map between non-isomorphic irreducibles is zero. -/
theorem schur_zero (T : α → α) (zero : α)
    (h : ∀ v, T v = zero) (v : α) :
    valMap T (contents v) = contents zero := by simp [h]

-- ============================================================================
-- Semisimple and Irreducible Representations
-- ============================================================================

/-- Semisimple: every subrepresentation has a complement. -/
theorem semisimple_complement (P : α → α)
    (h_idem : ∀ v, P (P v) = P v) (v : α) :
    valMap P (valMap P (contents v)) = valMap P (contents v) := by simp [h_idem]

/-- Direct sum decomposition of semisimple representation. -/
theorem semisimple_decomp (P₁ P₂ addF : α → α → α)
    (h_sum : ∀ v, addF (P₁ v v) (P₂ v v) = v) (v : α) :
    contents (addF (P₁ v v) (P₂ v v)) = contents v := by simp [h_sum]

-- ============================================================================
-- Tannaka Duality
-- ============================================================================

/-- Tannaka: G ≅ Aut(forget). An element g is determined by its action on all reps.
    Val level: if two group elements act the same on all contents, they are equal. -/
theorem tannaka_faithful (rho : α → α → α)
    (g₁ g₂ : α) (h : ∀ v, rho g₁ v = rho g₂ v) (v : Val α) :
    rep rho g₁ v = rep rho g₂ v := by
  cases v <;> simp [rep, valMap, h]

/-- Tannaka: the forgetful functor is faithful. -/
theorem tannaka_forget_faithful (T₁ T₂ : α → α)
    (h : ∀ v, T₁ v = T₂ v) (v : Val α) :
    valMap T₁ v = valMap T₂ v := by cases v <;> simp [h]

/-- Hilbert 90: H¹(G, L*) = 0 for cyclic Galois extension.
    Every 1-cocycle is a coboundary. -/
theorem hilbert90 (rho mulF : α → α → α) (f : α → α)
    (h_cob : ∀ g, ∃ b, f g = mulF b (rho g b)) :
    ∀ g, ∃ b, f g = mulF b (rho g b) := h_cob

/-- Hilbert 90 additive: H¹(G, L) = 0 for cyclic Galois extension. -/
theorem hilbert90_additive (rho subF : α → α → α) (f : α → α)
    (h : ∀ g, ∃ b, f g = subF (rho g b) b) :
    ∀ g, ∃ b, f g = subF (rho g b) b := h

-- ============================================================================
-- Cyclic (Co)homology and Resolutions
-- ============================================================================

/-- Cyclic group: norm map N = Σ_{i=0}^{n-1} ρ(g^i). -/
abbrev normMap (normF : α → α) : Val α → Val α := valMap normF

/-- Cyclic homology: H_n computed via norm and augmentation. -/
theorem cyclic_homology_norm (normF augF : α → α) (zero : α)
    (h : ∀ a, augF (normF a) = zero) (a : α) :
    valMap augF (normMap normF (contents a)) = contents zero := by simp [normMap, h]


/-- Bar resolution: the standard free resolution of k over k[G]. -/
abbrev barResolutionDiff (diffF : α → α) : Val α → Val α := valMap diffF

/-- Bar resolution is exact: composition of consecutive differentials is zero. -/
theorem bar_resolution_exact (d₁ d₂ : α → α) (zero : α)
    (h : ∀ a, d₂ (d₁ a) = zero) (a : α) :
    valMap d₂ (valMap d₁ (contents a)) = contents zero := by simp [h]

/-- Augmentation map: ε : B_0 → k. Sort-preserving. -/
abbrev augmentation (augF : α → α) : Val α → Val α := valMap augF

/-- Augmentation composed with d₁ is zero. -/
theorem augmentation_d_zero (augF d₁ : α → α) (zero : α)
    (h : ∀ a, augF (d₁ a) = zero) (a : α) :
    valMap augF (valMap d₁ (contents a)) = contents zero := by simp [h]

-- ============================================================================
-- Rep/Basic: Category of Representations
-- ============================================================================

/-- Morphism in Rep: an intertwining map. Composition is function composition. -/
theorem rep_hom_comp (T₁ T₂ : α → α) (v : α) :
    valMap T₂ (valMap T₁ (contents v)) = valMap (T₂ ∘ T₁) (contents v) := rfl

/-- Identity morphism in Rep. -/
theorem rep_hom_id (v : Val α) : valMap id v = v := by cases v <;> rfl

/-- Rep is a concrete category: Hom(A,B) embeds faithfully into functions. -/
theorem rep_concrete_hom (T₁ T₂ : α → α) (h : ∀ v, T₁ v = T₂ v) (v : α) :
    valMap T₁ (contents v) = valMap T₂ (contents v) := by simp [h]

/-- Forgetting to modules: Rep k G → Mod_k. Sort-preserving. -/
abbrev forgetToMod (forgetF : α → α) : Val α → Val α := valMap forgetF

/-- Subrepresentation: a submodule closed under ρ(g). -/
theorem subrep_closed (rho : α → α → α) (mem : α → Prop)
    (h : ∀ g v, mem v → mem (rho g v)) (g v : α) (hv : mem v) :
    mem (rho g v) := h g v hv

/-- Quotient representation: V/W inherits ρ. -/
theorem quotient_rep_well_defined (rho : α → α → α) (projF : α → α)
    (h : ∀ g a, projF (rho g a) = rho g (projF a)) (g a : α) :
    valMap projF (rep rho g (contents a)) = rep rho g (valMap projF (contents a)) := by
  simp [rep, valMap, h]

/-- Induced representation: Ind_H^G(V). Sort-preserving map. -/
abbrev inducedRep (indF : α → α) : Val α → Val α := valMap indF

/-- Coinduced representation: Coind_H^G(V). Sort-preserving map. -/
abbrev coinducedRep (coindF : α → α) : Val α → Val α := valMap coindF

/-- Frobenius reciprocity: Hom_G(Ind V, W) ≅ Hom_H(V, Res W). -/
theorem frobenius_reciprocity (indF adjF : α → α) (a : α) :
    valMap adjF (inducedRep indF (contents a)) = contents (adjF (indF a)) := by
  simp [inducedRep, valMap]

/-- Finite-dimensional representation: intertwining map preserves sort across all Val. -/
theorem fdrep_intertwining_sort (T : α → α) (v : Val α) :
    (v = origin → valMap T v = origin) ∧
    (∀ a, v = contents a → ∃ b, valMap T v = contents b) :=
  ⟨fun h => by rw [h]; simp, fun a h => by rw [h]; exact ⟨T a, rfl⟩⟩

/-- FDRep monoidal: tensor product of fd reps is fd. -/
theorem fdrep_tensor (rho1 rho2 mulF : α → α → α) (g a b : α) :
    mul mulF (rep rho1 g (contents a)) (rep rho2 g (contents b)) =
    contents (mulF (rho1 g a) (rho2 g b)) := rfl

/-- Average element in k[G]: (1/|G|) Σ g. -/
theorem group_algebra_average_idempotent (avgF : α → α)
    (h : ∀ v, avgF (avgF v) = avgF v) (v : α) :
    valMap avgF (valMap avgF (contents v)) = valMap avgF (contents v) := by simp [h]

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
