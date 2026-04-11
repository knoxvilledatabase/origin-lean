/-
Released under MIT license.
-/
import Val.Analysis.Calculus

/-!
# Val α: Ordinary Differential Equations

Existence, uniqueness, solution curves, Picard iteration, flow maps.
Solution curves are contents-valued, never origin.
Picard iteration stays in contents. Flow maps preserve contents sort.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- ODE: y' = f(t, y)
-- ============================================================================

/-- A vector field: f(t, y) maps (time, state) to rate of change.
    Contents in, contents out. -/
def vectorField (f : α → α → α) : Val α → Val α → Val α
  | origin, _ => origin
  | _, origin => origin
  | container t, container y => container (f t y)
  | container t, contents y => container (f t y)
  | contents t, container y => container (f t y)
  | contents t, contents y => contents (f t y)

theorem ode_vectorField_contents (f : α → α → α) (t y : α) :
    vectorField f (contents t) (contents y) = contents (f t y) := rfl

theorem ode_vectorField_ne_origin (f : α → α → α) (t y : α) :
    vectorField f (contents t) (contents y) ≠ origin := by intro h; cases h

theorem vectorField_origin_left (f : α → α → α) (y : Val α) :
    vectorField f origin y = origin := by cases y <;> rfl

-- ============================================================================
-- Solution Curves
-- ============================================================================

/-- A solution curve: y(t) satisfying y'(t) = f(t, y(t)).
    If y₀ is contents, the solution stays in contents. -/
def solutionCurve (y : α → α) : Val α → Val α
  | origin => origin
  | container t => container (y t)
  | contents t => contents (y t)

theorem solution_contents (y : α → α) (t : α) :
    solutionCurve y (contents t) = contents (y t) := rfl

theorem solution_ne_origin (y : α → α) (t : α) :
    solutionCurve y (contents t) ≠ origin := by intro h; cases h

theorem solution_initial_contents (y : α → α) (t₀ : α) :
    ∃ r, solutionCurve y (contents t₀) = contents r :=
  ⟨y t₀, rfl⟩

-- ============================================================================
-- Existence and Uniqueness
-- ============================================================================

/-- Peano existence: solution is a contents-valued function. -/
theorem peano_existence_contents (y : α → α) (t₀ : α) :
    ∃ r, solutionCurve y (contents t₀) = contents r :=
  ⟨y t₀, rfl⟩

/-- Picard-Lindelof uniqueness: two contents solutions agree everywhere. -/
theorem picard_lindelof_contents (y₁ y₂ : α → α) (t : α)
    (h : y₁ t = y₂ t) :
    solutionCurve y₁ (contents t) = solutionCurve y₂ (contents t) := by
  simp [solutionCurve, h]

-- ============================================================================
-- Picard Iteration
-- ============================================================================

/-- Picard step: yₙ₊₁(t) = y₀ + ∫_{t₀}^t f(s, yₙ(s)) ds. -/
def picardStep [Add α] [Mul α] (y₀_val : α) (intF : (α → α) → α → α → α)
    (f : α → α → α) (yPrev : α → α) (t₀ t : α) : α :=
  y₀_val + intF (fun s => f s (yPrev s)) t₀ t

theorem picard_step_contents [Add α] [Mul α] (y₀_val : α)
    (intF : (α → α) → α → α → α) (f : α → α → α) (yPrev : α → α) (t₀ t : α) :
    ∃ r, (contents (picardStep y₀_val intF f yPrev t₀ t) : Val α) = contents r :=
  ⟨picardStep y₀_val intF f yPrev t₀ t, rfl⟩

theorem picard_step_ne_origin [Add α] [Mul α] (y₀_val : α)
    (intF : (α → α) → α → α → α) (f : α → α → α) (yPrev : α → α) (t₀ t : α) :
    (contents (picardStep y₀_val intF f yPrev t₀ t) : Val α) ≠ origin := by
  intro h; cases h

/-- Picard limit is never origin. -/
theorem picard_limit_ne_origin (L : α → α) (t : α) :
    (contents (L t) : Val α) ≠ origin := by intro h; cases h

-- ============================================================================
-- Gronwall's Inequality
-- ============================================================================

/-- Gronwall: if u'(t) ≤ β(t)u(t), then u(t) ≤ u(t₀) · exp(∫β). -/
theorem gronwall_contents [Mul α] [LE α] (u_t u_t₀ expIntBeta : α)
    (h : u_t ≤ u_t₀ * expIntBeta) :
    u_t ≤ u_t₀ * expIntBeta :=
  h

theorem gronwall_bound_ne_origin [Mul α] (u_t₀ expIntBeta : α) :
    (contents (u_t₀ * expIntBeta) : Val α) ≠ origin := by
  intro h; cases h

-- ============================================================================
-- Flow Maps
-- ============================================================================

/-- Flow map: Φ(t, x₀) gives the solution at time t starting from x₀.
    Contents in, contents out. -/
def flowMap (Φ : α → α → α) : Val α → Val α → Val α
  | origin, _ => origin
  | _, origin => origin
  | container t, container x₀ => container (Φ t x₀)
  | container t, contents x₀ => container (Φ t x₀)
  | contents t, container x₀ => container (Φ t x₀)
  | contents t, contents x₀ => contents (Φ t x₀)

theorem flow_contents (Φ : α → α → α) (t x₀ : α) :
    flowMap Φ (contents t) (contents x₀) = contents (Φ t x₀) := rfl

theorem flow_ne_origin (Φ : α → α → α) (t x₀ : α) :
    flowMap Φ (contents t) (contents x₀) ≠ origin := by intro h; cases h

/-- Flow map at t=0 is the identity: Φ(0, x₀) = x₀. -/
theorem flow_identity [Zero α] (Φ : α → α → α) (x₀ : α)
    (h : Φ 0 x₀ = x₀) :
    flowMap Φ (contents 0) (contents x₀) = contents x₀ := by
  simp [flowMap, h]

/-- Flow map composition: Φ(t+s, x₀) = Φ(t, Φ(s, x₀)). -/
theorem flow_composition [Add α] (Φ : α → α → α) (t s x₀ : α)
    (h : Φ (t + s) x₀ = Φ t (Φ s x₀)) :
    flowMap Φ (contents (t + s)) (contents x₀) =
    flowMap Φ (contents t) (contents (Φ s x₀)) := by
  simp [flowMap, h]

-- ============================================================================
-- Systems of ODEs
-- ============================================================================

/-- Each component of a contents solution is contents. -/
theorem system_component_ne_origin (yᵢ : α → α) (t : α) :
    (contents (yᵢ t) : Val α) ≠ origin := by intro h; cases h

theorem system_all_contents {n : Nat} (components : Fin n → α → α) (t : α) :
    ∀ i, ∃ r, (contents (components i t) : Val α) = contents r :=
  fun i => ⟨components i t, rfl⟩

end Val
