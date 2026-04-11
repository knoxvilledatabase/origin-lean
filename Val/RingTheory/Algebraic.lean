/-
Released under MIT license.
-/
import Val.PolyRing
import Val.RingTheory.Core

/-!
# Val α: RingTheory — Algebraic Elements and Integral Closure

Algebraic elements, algebraic independence, integral closure, adjoined
elements, norm maps, and trace maps.

Key dissolution: "minimal polynomial has nonzero leading coefficient."
In Val α, contents coefficients are never origin. Structural.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Algebraic Elements
-- ============================================================================

-- An element a is algebraic if f(a) = 0 for some nonzero polynomial f.
-- In Val α: contents coefficients are "nonzero" by construction.

/-- Polynomial witness: coefficients in contents. -/
def polyWithContents (addF mulF : α → α → α) (zero : α)
    (coeffs : List α) (a : α) : Val α :=
  polyEval addF mulF zero (coeffs.map contents) (contents a)

theorem polyWithContents_single (addF mulF : α → α → α) (zero c₀ a : α) :
    polyWithContents addF mulF zero [c₀] a = contents c₀ := rfl

/-- Contents polynomial coefficient is never origin (the "nonzero" condition). -/
theorem contents_coeff_ne_origin (a : α) :
    (contents a : Val α) ≠ origin := by
  intro h; cases h

/-- Algebraic: some contents-coefficient polynomial evaluates to contents(0). -/
def isAlgebraic (addF mulF : α → α → α) (zero : α) (a : α) : Prop :=
  ∃ poly : List α, poly ≠ [] ∧
    polyWithContents addF mulF zero poly a = contents zero

-- ============================================================================
-- Algebraic Independence
-- ============================================================================

/-- Algebraically independent: no contents polynomial evaluates to origin. -/
theorem alg_independent (addF mulF : α → α → α) (zero : α) (a : α)
    (h : ∀ poly : List α, poly ≠ [] →
      polyWithContents addF mulF zero poly a ≠ origin) :
    ∀ poly : List α, poly ≠ [] →
      polyWithContents addF mulF zero poly a ≠ (origin : Val α) :=
  h

-- ============================================================================
-- Integral Closure
-- ============================================================================

/-- Monic polynomial: nonempty and leading coefficient is contents(1). -/
def isMonic (one : α) (poly : List (Val α)) (h : poly ≠ []) : Prop :=
  poly.getLast h = contents one

/-- Monic condition: contents(1) is never origin. -/
theorem monic_leading_ne_origin (one : α) (poly : List (Val α))
    (h : poly ≠ []) (hm : isMonic one poly h) :
    poly.getLast h ≠ (origin : Val α) := by
  rw [hm]; intro h; cases h

/-- Integral element: satisfies a monic polynomial. -/
def isIntegral (addF mulF : α → α → α) (zero one : α) (a : α) : Prop :=
  ∃ poly : List (Val α), ∃ hne : poly ≠ [], isMonic one poly hne ∧
    polyEval addF mulF zero poly (contents a) = contents zero

-- ============================================================================
-- Adjoin: R[a]
-- ============================================================================

/-- Element of R[a]: polynomial in a with contents coefficients. -/
def adjoinElem (addF mulF : α → α → α) (zero : α) (coeffs : List α) (a : α) : Val α :=
  polyEval addF mulF zero (coeffs.map contents) (contents a)

theorem adjoinElem_single (addF mulF : α → α → α) (zero c₀ a : α) :
    adjoinElem addF mulF zero [c₀] a = contents c₀ := rfl

-- ============================================================================
-- Norm Map
-- ============================================================================

/-- Norm map preserves sort. -/
def normMap (N : α → α) : Val α → Val α
  | origin => origin
  | container a => container (N a)
  | contents a => contents (N a)

theorem normMap_contents (N : α → α) (a : α) :
    normMap N (contents a) = contents (N a) := rfl

theorem normMap_origin (N : α → α) :
    normMap N (origin : Val α) = origin := rfl

theorem normMap_ne_origin (N : α → α) (a : α) :
    normMap N (contents a) ≠ (origin : Val α) := by
  intro h; cases h

/-- Norm is multiplicative within contents. -/
theorem normMap_mul (mulF : α → α → α) (N : α → α)
    (hN : ∀ a b, N (mulF a b) = mulF (N a) (N b)) (a b : α) :
    normMap N (mul mulF (contents a) (contents b)) =
    mul mulF (normMap N (contents a)) (normMap N (contents b)) := by
  show contents (N (mulF a b)) = contents (mulF (N a) (N b))
  rw [hN]

-- ============================================================================
-- Trace Map
-- ============================================================================

/-- Trace map preserves sort. -/
def traceMap (T : α → α) : Val α → Val α
  | origin => origin
  | container a => container (T a)
  | contents a => contents (T a)

theorem traceMap_contents (T : α → α) (a : α) :
    traceMap T (contents a) = contents (T a) := rfl

theorem traceMap_ne_origin (T : α → α) (a : α) :
    traceMap T (contents a) ≠ (origin : Val α) := by
  intro h; cases h

/-- Trace is additive within contents. -/
theorem traceMap_add (addF : α → α → α) (T : α → α)
    (hT : ∀ a b, T (addF a b) = addF (T a) (T b)) (a b : α) :
    traceMap T (add addF (contents a) (contents b)) =
    add addF (traceMap T (contents a)) (traceMap T (contents b)) := by
  show contents (T (addF a b)) = contents (addF (T a) (T b))
  rw [hT]

end Val
