/-
Released under MIT license.
-/
import Origin.Field

/-!
# Origin Module: Scalar Action on Option

Val needed Module.lean (79 lines) as Level 5 — the top of the
five-level class hierarchy. Scalar multiplication of α on β, with
origin absorbing on both sides.

Origin: scalar multiplication through Option. None absorbs (the
whole absorbs the parts from either side). Some computes. Cross-type
lift — same as liftBin₂ in physics.
-/

universe u
variable {α β : Type u}

-- ============================================================================
-- Scalar Multiplication on Option
-- ============================================================================

/-- Scalar multiplication: None on either side gives None.
    The whole absorbs the parts — whether the scalar or the vector
    is the whole, the result is the whole. -/
def oSmul (smulF : α → β → β) : Option α → Option β → Option β
  | none, _        => none
  | _, none        => none
  | some r, some v => some (smulF r v)

-- ============================================================================
-- Simp Set
-- ============================================================================

@[simp] theorem oSmul_none_left (smulF : α → β → β) (v : Option β) :
    oSmul smulF none v = none := by cases v <;> rfl

@[simp] theorem oSmul_none_right (smulF : α → β → β) (r : Option α) :
    oSmul smulF r none = none := by cases r <;> rfl

@[simp] theorem oSmul_some (smulF : α → β → β) (r : α) (v : β) :
    oSmul smulF (some r) (some v) = some (smulF r v) := rfl

-- ============================================================================
-- Lifted Module Laws
-- ============================================================================

theorem oSmul_assoc
    (smulF : α → β → β) (mulF : α → α → α)
    (h : ∀ r s v, smulF r (smulF s v) = smulF (mulF r s) v)
    (r s : α) (v : β) :
    oSmul smulF (some r) (oSmul smulF (some s) (some v)) =
    oSmul smulF (some (mulF r s)) (some v) := by
  simp [oSmul, h]

theorem oSmul_add
    (smulF : α → β → β) (addF : β → β → β)
    (h : ∀ r u v, smulF r (addF u v) = addF (smulF r u) (smulF r v))
    (r : α) (u v : β) :
    oSmul smulF (some r) (some (addF u v)) =
    some (addF (smulF r u) (smulF r v)) := by
  simp [oSmul, h]

theorem oOne_smul
    (smulF : α → β → β) (one : α)
    (h : ∀ v : β, smulF one v = v)
    (v : β) :
    oSmul smulF (some one) (some v) = some v := by
  simp [oSmul, h]

-- ============================================================================
-- The Count
-- ============================================================================

-- Val/Module.lean: 79 lines. Level 5 of 5. Required ValField + ValArith
-- + ValModule typeclass. 6 pattern matches (3 constructors × 2 sides).
--
-- Origin/Module.lean: this file. No typeclasses. Functions as parameters.
-- 2 pattern matches (None/Some × 2 sides).
--
-- The five-level class hierarchy is now fully replaced:
--
--   Val                         Origin
--   Foundation.lean (166)  →  (standard library: Option)
--   Arith.lean (155)       →  (absorbed into Ring.lean)
--   Ring.lean (140)        →  Ring.lean (128)
--   Field.lean (94)        →  Field.lean (142)
--   OrderedField.lean (79) →  OrderedField.lean
--   Module.lean (79)       →  Module.lean (this file)
--
--   Val total: 713 lines, 6 files, 5 custom typeclasses
--   Origin total: 4 files, 0 custom typeclasses, 0 custom types
