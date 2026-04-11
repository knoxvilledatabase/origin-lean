/-
Released under MIT license.
-/
import Val.Algebra

/-!
# Vector Spaces and Modules on Val α

Scalar multiplication (smul), module laws, sort preservation.
The module lives entirely in contents. Origin and container are outside by type.
-/

namespace Val

universe u
variable {α β : Type u}

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

/-- Contents scalar × contents vector = contents. Always. -/
theorem smul_contents_ne_origin (f : α → β → β) (a : α) (v : β) :
    smul f (contents a) (contents v) ≠ (origin : Val β) := by simp

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

end Val
