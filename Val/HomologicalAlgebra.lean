/-
Released under MIT license.
-/
import Val.Category.Core
import Val.RingTheory.Core
import Val.Algebra

/-!
# Val α: Homological Algebra

Chain complexes, homology, exact sequences, derived functors, Ext/Tor.
The sort propagates through differentials, kernels, images, and derived functors.
Everything stays in contents. Origin is outside all chain groups.
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

/-- Differentials map contents to contents. -/
theorem differential_contents (C : ChainComplex α) (n : Int) (a : α) :
    valMap (C.differential n) (contents a) = contents (C.differential n a) := rfl

/-- Differentials never produce origin from contents input. -/
theorem differential_ne_origin (C : ChainComplex α) (n : Int) (a : α) :
    (contents (C.differential n a) : Val α) ≠ origin := by intro h; cases h

-- ============================================================================
-- d² = 0: The Boundary of a Boundary Is Zero
-- ============================================================================

/-- d² = 0 in α lifts to contents(0) in Val α, not origin. -/
theorem d_squared_contents [Zero α] (C : ChainComplex α) (n : Int) (a : α)
    (h : C.differential (n - 1) (C.differential n a) = 0) :
    (contents (C.differential (n - 1) (C.differential n a)) : Val α) = contents 0 := by
  congr 1

/-- d²(a) is contents(0), not origin. Inaction, not absorption. -/
theorem d_squared_ne_origin [Zero α] (C : ChainComplex α) (n : Int) (a : α)
    (_ : C.differential (n - 1) (C.differential n a) = 0) :
    (contents (C.differential (n - 1) (C.differential n a)) : Val α) ≠ origin := by
  intro h; cases h

-- ============================================================================
-- Kernel and Image
-- ============================================================================

/-- Kernel: elements a where d(a) = zero. -/
def inKernel (d : α → α) (zero : α) (a : α) : Prop := d a = zero

/-- Image: elements a where a = d(b) for some b. -/
def inImage (d : α → α) (a : α) : Prop := ∃ b, d b = a

/-- Kernel elements are contents. -/
theorem kernel_contents (d : α → α) (zero : α) (a : α) (_ : inKernel d zero a) :
    ∃ r, (contents a : Val α) = contents r := ⟨a, rfl⟩

/-- Homology class: quotient map sends contents to contents. -/
theorem homology_class_contents (proj : α → α) (a : α) :
    quotientMap proj (contents a) = contents (proj a) := rfl

/-- Homology class is never origin. -/
theorem homology_class_ne_origin (proj : α → α) (a : α) :
    quotientMap proj (contents a) ≠ origin := by simp [quotientMap]

-- ============================================================================
-- Exact Sequences
-- ============================================================================

/-- Exact at position n: im(dₙ₊₁) = ker(dₙ). -/
def isExact (d_next d_curr : α → α) (zero : α) : Prop :=
  ∀ a, inImage d_next a ↔ inKernel d_curr zero a

/-- In an exact sequence, every kernel element has a contents preimage. -/
theorem exact_preimage_contents (d_next d_curr : α → α) (zero : α)
    (h : isExact d_next d_curr zero) (a : α) (hk : inKernel d_curr zero a) :
    ∃ b, d_next b = a ∧ (contents b : Val α) ≠ origin :=
  let ⟨b, hb⟩ := (h a).mpr hk
  ⟨b, hb, by intro h2; cases h2⟩

-- ============================================================================
-- Derived Functors
-- ============================================================================

/-- valMap lifts functors to chain complexes. Contents in, contents out. -/
theorem derived_functor_contents (F : α → α) (a : α) :
    valMap F (contents a) = contents (F a) := rfl

/-- Derived functor never sends contents to origin. -/
theorem derived_functor_ne_origin (F : α → α) (a : α) :
    valMap F (contents a) ≠ (origin : Val α) := by intro h; cases h

/-- Derived functor preserves composition. -/
theorem derived_functor_comp (F G : α → α) :
    valMap (G ∘ F) = valMap G ∘ valMap F := valMap_comp F G

-- ============================================================================
-- Ext and Tor
-- ============================================================================

/-- Ext: Hom applied to a resolution element. Contents in, contents out. -/
theorem ext_contents (homF : α → α → α) (a b : α) :
    ∃ r, (contents (homF a b) : Val α) = contents r := ⟨homF a b, rfl⟩

/-- Tor: tensor of contents with contents is contents (multiplication). -/
theorem tor_contents (mulF : α → α → α) (a b : α) :
    mul mulF (contents a) (contents b) = contents (mulF a b) := rfl

/-- Tor is never origin from contents inputs. -/
theorem tor_ne_origin (mulF : α → α → α) (a b : α) :
    mul mulF (contents a) (contents b) ≠ origin := by simp

-- ============================================================================
-- Long Exact Sequence
-- ============================================================================

/-- The connecting homomorphism δ maps contents to contents. -/
theorem connecting_homomorphism_contents (delta : α → α) (a : α) :
    valMap delta (contents a) = contents (delta a) := rfl

/-- Each map in the long exact sequence preserves sort. -/
theorem long_exact_sort_preserved (f : α → α) (a : α) :
    ∃ r, valMap f (contents a) = contents r := ⟨f a, rfl⟩

end Val
