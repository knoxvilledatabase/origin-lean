/-
Released under MIT license.
-/
import Val.Field

/-!
# Val α: Level 5 — ValModule (Scalar Action)

Two-type class. A module of β over α: scalar multiplication of α on β.
Extends ValField α (scalars are a field) and ValArith β (vectors have operations).

Domains: LinearAlgebra, FunctionalAnalysis, RepresentationTheory, DifferentialGeometry.
-/

namespace Val

universe u
variable {α β : Type u}

-- ============================================================================
-- The Module Class
-- ============================================================================

class ValModule (α β : Type u) [ValField α] [ValArith β] where
  smulF : α → β → β
  smul_assoc : ∀ (r s : α) (v : β), smulF r (smulF s v) = smulF (ValArith.mulF r s) v
  smul_add : ∀ (r : α) (u v : β), smulF r (ValArith.addF u v) = ValArith.addF (smulF r u) (smulF r v)
  add_smul : ∀ (r s : α) (v : β), smulF (ValArith.addF r s) v = ValArith.addF (smulF r v) (smulF s v)
  one_smul : ∀ v : β, smulF ValField.one v = v

-- ============================================================================
-- Scalar Multiplication on Val
-- ============================================================================

def smul [ValArith α] [ValArith β] [ValField α] [ValModule α β] :
    Val α → Val β → Val β
  | origin, _                  => origin
  | _, origin                  => origin
  | container r, container v   => container (ValModule.smulF r v)
  | container r, contents v    => container (ValModule.smulF r v)
  | contents r, container v    => container (ValModule.smulF r v)
  | contents r, contents v     => contents (ValModule.smulF r v)

-- ============================================================================
-- Simp Set: smul
-- ============================================================================

@[simp] theorem smul_origin_left [ValArith α] [ValArith β] [ValField α] [ValModule α β]
    (v : Val β) : smul (origin : Val α) v = origin := by cases v <;> rfl

@[simp] theorem smul_origin_right [ValArith α] [ValArith β] [ValField α] [ValModule α β]
    (r : Val α) : smul r (origin : Val β) = origin := by cases r <;> rfl

@[simp] theorem smul_contents_contents [ValArith α] [ValArith β] [ValField α] [ValModule α β]
    (r : α) (v : β) :
    smul (contents r) (contents v) = contents (ValModule.smulF r v) := rfl

-- ============================================================================
-- Lifted Module Laws
-- ============================================================================

theorem val_smul_assoc [ValField α] [ValArith β] [ValModule α β]
    (r s : α) (v : β) :
    smul (contents r) (smul (contents s) (contents v)) =
    smul (contents (ValArith.mulF r s)) (contents v) := by
  simp [smul, ValModule.smul_assoc]

theorem val_smul_add [ValField α] [ValArith β] [ValModule α β]
    (r : α) (u v : β) :
    smul (contents r) (add (contents u) (contents v)) =
    add (smul (contents r) (contents u)) (smul (contents r) (contents v)) := by
  simp [smul, add, ValModule.smul_add]

theorem val_one_smul [ValField α] [ValArith β] [ValModule α β]
    (v : β) :
    smul (contents (ValField.one (α := α))) (contents v) = contents v := by
  simp [smul, ValModule.one_smul]

end Val
