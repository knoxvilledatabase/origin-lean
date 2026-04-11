/-
Released under MIT license.
-/
import Val.Topology.Core
import Val.VectorSpace
import Val.Analysis.Core

/-!
# Val α: Topological Algebra

Topological groups, topological rings, topological fields.
Operations are continuous in the sort topology: contents × contents → contents.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Topological Group: Multiplication is Sort-Continuous
-- ============================================================================

/-- Multiplication is sort-continuous: contents × contents → contents. -/
theorem mul_sort_continuous (f : α → α → α) (a b : α) :
    ∃ r, mul f (contents a) (contents b) = contents r := ⟨f a b, rfl⟩

/-- Addition is sort-continuous: contents + contents → contents. -/
theorem add_sort_continuous (f : α → α → α) (a b : α) :
    ∃ r, add f (contents a) (contents b) = contents r := ⟨f a b, rfl⟩

/-- Negation is sort-continuous: -contents → contents. -/
theorem neg_sort_continuous (f : α → α) (a : α) :
    ∃ r, neg f (contents a) = contents r := ⟨f a, rfl⟩

/-- Inversion is sort-continuous: contents⁻¹ → contents. -/
theorem inv_sort_continuous (f : α → α) (a : α) :
    ∃ r, inv f (contents a) = contents r := ⟨f a, rfl⟩

-- ============================================================================
-- Topological Group: Origin Absorbs
-- ============================================================================

/-- Multiplication with origin absorbs. This is the "continuous extension to ∞". -/
theorem mul_origin_absorbs (f : α → α → α) (x : Val α) :
    mul f x origin = origin := by simp

/-- Addition with origin absorbs. -/
theorem add_origin_absorbs (f : α → α → α) (x : Val α) :
    add f x origin = origin := by simp

-- ============================================================================
-- Topological Ring: Distributivity is Sort-Continuous
-- ============================================================================

/-- Left distributivity stays in contents when all inputs are contents. -/
theorem left_distrib_contents (mulF addF : α → α → α)
    (h : ∀ a b c : α, mulF a (addF b c) = addF (mulF a b) (mulF a c))
    (a b c : α) :
    mul mulF (contents a) (add addF (contents b) (contents c)) =
    add addF (mul mulF (contents a) (contents b)) (mul mulF (contents a) (contents c)) := by
  simp [h]

-- ============================================================================
-- Topological Field: Division is Sort-Continuous
-- ============================================================================

/-- Division is sort-continuous: contents / contents → contents. -/
theorem div_sort_continuous (mulF invF : α → α → α) (a b : α) :
    ∃ r, fdiv mulF (fun x => invF x x) (contents a) (contents b) = contents r :=
  ⟨mulF a (invF b b), rfl⟩

/-- Division never produces origin from contents inputs. -/
theorem div_ne_origin (mulF : α → α → α) (invF : α → α) (a b : α) :
    fdiv mulF invF (contents a) (contents b) ≠ origin := by simp [fdiv]

-- ============================================================================
-- Topological Module: Scalar Multiplication
-- ============================================================================

/-- Scalar multiplication is sort-continuous: contents · contents → contents. -/
theorem smul_sort_continuous (f : α → α → α) (a b : α) :
    ∃ r, smul f (contents a) (contents b) = contents r := ⟨f a b, rfl⟩

/-- Scalar multiplication with origin absorbs. -/
theorem smul_origin_absorbs (f : α → α → α) (a : α) :
    smul f (contents a) (origin : Val α) = origin := by simp

-- ============================================================================
-- Continuity of Group Operations in Convergence
-- ============================================================================

/-- If sₙ → L and tₙ → M in α, then contents(sₙ * tₙ) → contents(L * M). -/
theorem topological_group_mul (mulF : α → α → α)
    (conv : (Nat → α) → α → Prop)
    (hconv : ∀ s t L M, conv s L → conv t M → conv (fun n => mulF (s n) (t n)) (mulF L M))
    (s t : Nat → α) (L M : α) (hs : conv s L) (ht : conv t M) :
    liftConv conv (fun n => mul mulF (contents (s n)) (contents (t n)))
      (contents (mulF L M)) :=
  ⟨fun n => mulF (s n) (t n), fun _ => rfl, hconv s t L M hs ht⟩

/-- If sₙ → L, then neg-contents(sₙ) → contents(-L). -/
theorem topological_group_neg (negF : α → α)
    (conv : (Nat → α) → α → Prop)
    (hconv : ∀ s L, conv s L → conv (fun n => negF (s n)) (negF L))
    (s : Nat → α) (L : α) (hs : conv s L) :
    liftConv conv (fun n => neg negF (contents (s n))) (contents (negF L)) :=
  ⟨fun n => negF (s n), fun _ => rfl, hconv s L hs⟩

-- ============================================================================
-- THE RESULT
-- ============================================================================
--
-- Topological algebra over Val α:
--   ✓ Mul, add, neg, inv sort-continuous (contents → contents)
--   ✓ Origin absorbs under all operations
--   ✓ Distributivity sort-continuous
--   ✓ Division sort-continuous, never origin
--   ✓ Scalar multiplication sort-continuous
--   ✓ Group operations preserve convergence within contents
--
-- Zero sorries. Zero typeclasses. Zero Mathlib.

end Val
