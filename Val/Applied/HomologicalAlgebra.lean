/-
Released under MIT license.
-/
import Val.Algebra.Core
import Val.Category.Core

/-!
# Val α: Applied — Homological Algebra

Chain complexes, homology, exact sequences, derived functors.
-/

namespace Val

universe u

variable {α : Type u}

-- ============================================================================
-- Chain Complexes
-- ============================================================================

/-- A chain complex: sequence of modules with differentials d : Cₙ → Cₙ₋₁. -/
structure ChainComplex (α : Type u) where
  differential : Int → α → α

-- ============================================================================
-- d² = 0: The Boundary of a Boundary Is Zero
-- ============================================================================

/-- d² = 0 in α lifts to contents(0) in Val α, not origin. -/
theorem d_squared_contents [Zero α] (C : ChainComplex α) (n : Int) (a : α)
    (h : C.differential (n - 1) (C.differential n a) = 0) :
    (contents (C.differential (n - 1) (C.differential n a)) : Val α) = contents 0 := by
  congr 1


-- ============================================================================
-- Kernel and Image
-- ============================================================================

/-- Kernel: elements a where d(a) = zero. -/
def inKernel (d : α → α) (zero : α) (a : α) : Prop := d a = zero

/-- Image: elements a where a = d(b) for some b. -/
def inImage (d : α → α) (a : α) : Prop := ∃ b, d b = a

-- ============================================================================
-- Exact Sequences
-- ============================================================================

/-- Exact at position n: im(dₙ₊₁) = ker(dₙ). Same-type version for chain complexes. -/
def isExactChain (d_next d_curr : α → α) (zero : α) : Prop :=
  ∀ a, inImage d_next a ↔ inKernel d_curr zero a

/-- In an exact sequence, every kernel element has a contents preimage. -/
theorem exact_preimage_contents (d_next d_curr : α → α) (zero : α)
    (h : isExactChain d_next d_curr zero) (a : α) (hk : inKernel d_curr zero a) :
    ∃ b, d_next b = a ∧ (contents b : Val α) ≠ origin :=
  let ⟨b, hb⟩ := (h a).mpr hk
  ⟨b, hb, by intro h2; cases h2⟩

-- ============================================================================
-- Derived Functors
-- ============================================================================

-- derived_functor_contents and derived_functor_comp: see Category.lean

-- ============================================================================
-- Ext and Tor
-- ============================================================================

-- ============================================================================
-- Long Exact Sequence
-- ============================================================================

end Val
