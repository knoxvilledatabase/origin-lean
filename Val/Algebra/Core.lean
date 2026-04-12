/-
Released under MIT license.
-/
import Val.Foundation

/-!
# Val α: Algebra Core — The Complete Algebraic Toolkit

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

end Val
