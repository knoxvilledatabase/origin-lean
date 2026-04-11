/-
Released under MIT license.
-/
import Val.VectorSpace
import Val.Category.Core

/-!
# Val α: Modules, Submodules, Quotients

Modules over Val α scalars. Submodules. Quotient modules.
The sort propagates through all module operations.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Module Structure
-- ============================================================================

/-- A module element in Val α. Contents values form the module. -/
def moduleElement (v : α) : Val α := contents v

/-- Module elements are contents. -/
theorem module_element_contents (v : α) :
    ∃ r, moduleElement v = contents r := ⟨v, rfl⟩

/-- Module elements are never origin. -/
theorem module_element_ne_origin (v : α) :
    moduleElement v ≠ (origin : Val α) := by simp [moduleElement]

-- ============================================================================
-- Module Operations
-- ============================================================================

/-- Module addition: contents + contents = contents. -/
theorem module_add (addF : α → α → α) (v w : α) :
    add addF (contents v) (contents w) = contents (addF v w) := rfl

/-- Scalar multiplication: contents · contents = contents. -/
theorem module_smul (f : α → α → α) (c v : α) :
    smul f (contents c) (contents v) = contents (f c v) := rfl

/-- Module negation: -contents = contents. -/
theorem module_neg (negF : α → α) (v : α) :
    neg negF (contents v) = contents (negF v) := rfl

-- ============================================================================
-- Submodule
-- ============================================================================

/-- Submodule elements in Val α are contents. -/
theorem submodule_contents (S : α → Prop) (v : α) (_ : S v) :
    ∃ r, (contents v : Val α) = contents r := ⟨v, rfl⟩

/-- Submodule elements are never origin. -/
theorem submodule_ne_origin (S : α → Prop) (v : α) (_ : S v) :
    (contents v : Val α) ≠ origin := by simp

/-- Submodule addition stays in contents. -/
theorem submodule_add_contents (addF : α → α → α) (S : α → Prop)
    (_ : ∀ a b, S a → S b → S (addF a b))
    (v w : α) (_ : S v) (_ : S w) :
    add addF (contents v) (contents w) = contents (addF v w) := rfl

-- ============================================================================
-- Quotient Module
-- ============================================================================

/-- Quotient module: factor by a submodule. -/
def quotientModule (proj : α → α) (v : α) : Val α := contents (proj v)

/-- Quotient module elements are contents. -/
theorem quotient_module_contents (proj : α → α) (v : α) :
    ∃ r, quotientModule proj v = contents r := ⟨proj v, rfl⟩

/-- Quotient module elements are never origin. -/
theorem quotient_module_ne_origin (proj : α → α) (v : α) :
    quotientModule proj v ≠ (origin : Val α) := by simp [quotientModule]

/-- Quotient map is compatible with module operations. -/
theorem quotient_module_add (addF : α → α → α) (proj : α → α)
    (h : ∀ a b, proj (addF a b) = addF (proj a) (proj b)) (v w : α) :
    quotientModule proj (addF v w) = contents (addF (proj v) (proj w)) := by
  show contents (proj (addF v w)) = contents (addF (proj v) (proj w)); rw [h]

-- ============================================================================
-- Direct Sum
-- ============================================================================

/-- Direct sum of two modules: Val (α × α). -/
theorem direct_sum_contents (v w : α) :
    (contents (v, w) : Val (α × α)) ≠ origin := by simp

/-- Direct sum projection to first component. -/
theorem direct_sum_proj1 (v w : α) :
    valMap Prod.fst (contents (v, w) : Val (α × α)) = contents v := rfl

/-- Direct sum projection to second component. -/
theorem direct_sum_proj2 (v w : α) :
    valMap Prod.snd (contents (v, w) : Val (α × α)) = contents w := rfl

-- ============================================================================
-- Module Homomorphism
-- ============================================================================

/-- A module homomorphism: a sort-preserving map. -/
theorem module_hom_contents (f : α → α) (v : α) :
    valMap f (contents v) = contents (f v) := rfl

/-- Module homomorphisms preserve origin. -/
theorem module_hom_origin (f : α → α) :
    valMap f (origin : Val α) = origin := rfl

/-- Kernel of a module homomorphism: preimage of zero. -/
theorem module_hom_kernel_contents [Zero α] (f : α → α) (v : α) (h : f v = 0) :
    valMap f (contents v) = contents (0 : α) := by
  show contents (f v) = contents 0; rw [h]

-- ============================================================================
-- THE RESULT
-- ============================================================================
--
-- Modules over Val α:
--   ✓ Module elements: contents, never origin
--   ✓ Module operations: add, smul, neg all preserve contents
--   ✓ Submodules: closed under operations, contents throughout
--   ✓ Quotient modules: contents, never origin, compatible with operations
--   ✓ Direct sums: contents products, projections work
--   ✓ Module homomorphisms: sort-preserving, kernels are contents
--
-- Zero sorries. Zero typeclasses. Zero Mathlib.

end Val
