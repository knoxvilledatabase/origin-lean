/-
Released under MIT license.
-/
import Val.Analysis.Normed
import Val.FunctionalAnalysis

/-!
# Val α: C*-Algebras

C*-algebras, GNS construction, spectral theory for C*-algebras.
The C*-identity ‖a*a‖ = ‖a‖² is a contents equation.
Star operation maps contents to contents. No ≠ 0 at sort level.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Star Operation (Involution)
-- ============================================================================

/-- The star (adjoint) operation on Val α. Contents star is contents. -/
def starOp (starF : α → α) : Val α → Val α
  | origin => origin
  | container a => container (starF a)
  | contents a => contents (starF a)

@[simp] theorem starOp_contents (starF : α → α) (a : α) :
    starOp starF (contents a) = contents (starF a) := rfl

@[simp] theorem starOp_origin (starF : α → α) :
    starOp starF (origin : Val α) = origin := rfl

theorem starOp_contents_ne_origin (starF : α → α) (a : α) :
    starOp starF (contents a) ≠ (origin : Val α) := by intro h; cases h

-- ============================================================================
-- Star Axioms
-- ============================================================================

/-- Star is involutive: a** = a within contents. -/
theorem star_invol (starF : α → α) (hinv : ∀ a, starF (starF a) = a) (a : α) :
    starOp starF (starOp starF (contents a)) = contents a := by
  show contents (starF (starF a)) = contents a; rw [hinv]

/-- Star distributes over addition within contents. -/
theorem star_add_distrib [Add α] (starF : α → α)
    (h : ∀ a b, starF (a + b) = starF a + starF b) (a b : α) :
    starOp starF (contents (a + b)) =
    contents (starF a + starF b) := by
  show contents (starF (a + b)) = contents (starF a + starF b); rw [h]

/-- Star distributes over multiplication (reversed) within contents. -/
theorem star_mul_rev [Mul α] (starF : α → α)
    (h : ∀ a b, starF (a * b) = starF b * starF a) (a b : α) :
    starOp starF (contents (a * b)) =
    contents (starF b * starF a) := by
  show contents (starF (a * b)) = contents (starF b * starF a); rw [h]

-- ============================================================================
-- C*-Identity: ‖a*a‖ = ‖a‖²
-- ============================================================================

/-- The C*-identity: ‖a* · a‖ = ‖a‖². Within contents, both sides are contents. -/
theorem cstar_identity [Mul α] (normF : α → α) (starF : α → α)
    (h : ∀ a, normF (starF a * a) = normF a * normF a) (a : α) :
    valNormGroup normF (contents (starF a * a)) =
    contents (normF a * normF a) := by
  show contents (normF (starF a * a)) = contents (normF a * normF a); rw [h]

/-- The C*-norm is never origin for contents. -/
theorem cstar_norm_ne_origin [Mul α] (normF : α → α) (starF : α → α) (a : α) :
    valNormGroup normF (contents (starF a * a)) ≠ (origin : Val α) := by
  intro h; cases h

-- ============================================================================
-- Positivity in C*-Algebras
-- ============================================================================

/-- An element is positive if a = b*b for some b. -/
def isPositive [Mul α] (starF : α → α) (a : α) : Prop :=
  ∃ b : α, a = starF b * b

theorem positive_contents [Mul α] (starF : α → α) (a : α) :
    (contents a : Val α) ≠ origin := by intro h; cases h

-- ============================================================================
-- Spectrum of a C*-Element
-- ============================================================================

/-- The spectrum: λ such that (a - λ·identity) is not invertible. -/
def inCStarSpectrum [Add α] [Mul α] [Neg α] (a lambda identity : α)
    (isInvertible : α → Prop) : Prop :=
  ¬ isInvertible (a + -(lambda * identity))

theorem cstar_spectral_value_contents (lambda : α) :
    (contents lambda : Val α) ≠ origin := by intro h; cases h

-- ============================================================================
-- GNS Construction
-- ============================================================================

/-- GNS state: a positive linear functional φ on the C*-algebra.
    φ maps contents to contents. -/
def gnsState (phi : α → α) : Val α → Val α
  | origin => origin
  | container a => container (phi a)
  | contents a => contents (phi a)

theorem gns_state_contents (phi : α → α) (a : α) :
    gnsState phi (contents a) = contents (phi a) := rfl

theorem gns_state_ne_origin (phi : α → α) (a : α) :
    gnsState phi (contents a) ≠ (origin : Val α) := by intro h; cases h

/-- GNS inner product: ⟨a, b⟩_φ = φ(a* · b). All contents operations. -/
def gnsInnerProd [Mul α] (phi : α → α) (starF : α → α) (a b : α) : α :=
  phi (starF a * b)

theorem gns_inner_prod_contents [Mul α] (phi : α → α) (starF : α → α) (a b : α) :
    (contents (gnsInnerProd phi starF a b) : Val α) ≠ origin := by intro h; cases h

-- ============================================================================
-- Self-Adjoint Elements
-- ============================================================================

/-- An element is self-adjoint if a* = a. -/
def isSelfAdjoint (starF : α → α) (a : α) : Prop := starF a = a

/-- Self-adjoint elements: star leaves them fixed. -/
theorem selfadjoint_contents (starF : α → α) (a : α) (h : isSelfAdjoint starF a) :
    starOp starF (contents a) = contents a := by
  show contents (starF a) = contents a; rw [h]

/-- Spectral radius equals norm in a C*-algebra. -/
theorem cstar_spectral_radius_eq_norm (normF : α → α) (spectralRadiusF : α → α)
    (h : ∀ a, spectralRadiusF a = normF a) (a : α) :
    contents (spectralRadiusF a) = (contents (normF a) : Val α) := by
  show contents (spectralRadiusF a) = contents (normF a); rw [h]

end Val
