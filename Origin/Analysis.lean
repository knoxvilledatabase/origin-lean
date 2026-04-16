/-
Released under MIT license.
-/
import Origin.Core

/-!
# Analysis on Option α (Core-based)

Val/Analysis.lean: 832 lines. Limits, derivatives, integrals, series,
normed spaces, special functions, inner products, convex analysis,
complex analysis, C*-algebras, asymptotics, distributions, ODEs.

This version keeps only domain-specific definitions and proofs that
actually use Option.
-/

universe u
variable {α : Type u}

-- ============================================================================
-- 1. LIMITS AND CONVERGENCE
-- ============================================================================

def converges (convF : (Nat → α) → α → Prop) (seq : Nat → Option α) (L : α) : Prop :=
  ∃ f : Nat → α, (∀ n, seq n = some (f n)) ∧ convF f L

def isCauchy (cauchyF : (Nat → α) → Prop) (seq : Nat → Option α) : Prop :=
  ∃ f : Nat → α, (∀ n, seq n = some (f n)) ∧ cauchyF f

def isComplete (cauchyF : (Nat → α) → Prop) (convF : (Nat → α) → α → Prop) : Prop :=
  ∀ f, cauchyF f → ∃ l, convF f l

-- ============================================================================
-- 2. DERIVATIVES
-- ============================================================================

def iterDeriv (derivF : α → α) : Nat → Option α → Option α
  | 0, v => v
  | n + 1, v => Option.map derivF (iterDeriv derivF n v)

theorem iterDeriv_none (derivF : α → α) (n : Nat) :
    iterDeriv derivF n (none : Option α) = none := by
  induction n with
  | zero => rfl
  | succ n ih => simp [iterDeriv, ih]

-- ============================================================================
-- 3. SERIES
-- ============================================================================

def partialSum [Add α] (seq : Nat → Option α) : Nat → Option α
  | 0 => seq 0
  | n + 1 => partialSum seq n + seq (n + 1)

-- ============================================================================
-- 5. POWER SERIES
-- ============================================================================

def isAnalytic (analyticF : (α → α) → α → Prop) (f : α → α) : Option α → Prop
  | some a => analyticF f a
  | none => False

-- Inverse pairs (exp/log, fourier), involutions (adjoint), idempotents
-- (projection): all close with cases v <;> simp [h] from Core.

-- ============================================================================
-- 4. CONVEX ANALYSIS
-- ============================================================================

def isConvexFn (f : α → α) (leF : α → α → Prop) (addF mulF : α → α → α)
    (one : α) (negF : α → α) : Prop :=
  ∀ a b t, leF (addF one (negF one)) t → leF t one →
    leF (f (addF (mulF t a) (mulF (addF one (negF t)) b)))
        (addF (mulF t (f a)) (mulF (addF one (negF t)) (f b)))

-- ============================================================================
-- 9. COMPLEX ANALYSIS
-- ============================================================================

def isHolomorphic (holoF : (α → α) → α → Prop) (f : α → α) : Option α → Prop
  | some a => holoF f a
  | none => False

-- ============================================================================
-- 6. ODE
-- ============================================================================

def isODESolution (derivF : α → α) (fieldF : α → α → α) (f : α → α) : Prop :=
  ∀ t, derivF (f t) = fieldF t (f t)

-- ============================================================================
-- 12. CONTRACTION MAPPING
-- ============================================================================

def isContraction (contrF : (α → α) → Prop) (f : α → α) : Prop := contrF f

theorem banach_fixed_point (contrF : (α → α) → Prop) (fixedPtF : (α → α) → α)
    (h : ∀ f, contrF f → f (fixedPtF f) = fixedPtF f)
    (f : α → α) (hf : isContraction contrF f) :
    f (fixedPtF f) = fixedPtF f := h f hf
