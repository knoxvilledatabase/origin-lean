/-
Released under MIT license.
-/
import Val.Physics.Dimension

/-!
# Val Physics: Classical Mechanics

The first domain file. Two mechanisms working together:
- Val's sort dispatch handles existence boundaries (singularities)
- Lean's type system handles dimensional consistency

Every theorem carries zero existence-boundary hypotheses AND zero
dimensional-consistency hypotheses. The sort dispatch handles the first.
The type system handles the second.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Part 1: Newton's Second Law — F = ma
-- ============================================================================

-- Dimensional: force = mass × acceleration.
-- Existence: if mass or acceleration is not in the counting domain, neither is force.

def newtonForce [ValArith α]
    (mass : Val (Quantity Dim.M α))
    (accel : Val (Quantity Dim.acceleration α)) :
    Val (Quantity Dim.force α) :=
  mulQ mass accel

/-- Mass not in counting domain: neither is force. No hypothesis. -/
theorem newton_mass_origin [ValArith α]
    (accel : Val (Quantity Dim.acceleration α)) :
    newtonForce (origin : Val (Quantity Dim.M α)) accel = origin := by
  simp [newtonForce]

/-- Acceleration not in counting domain: neither is force. No hypothesis. -/
theorem newton_accel_origin [ValArith α]
    (mass : Val (Quantity Dim.M α)) :
    newtonForce mass (origin : Val (Quantity Dim.acceleration α)) = origin := by
  simp [newtonForce]

/-- Both defined: computes. -/
theorem newton_contents [ValArith α]
    (m : Quantity Dim.M α) (a : Quantity Dim.acceleration α) :
    newtonForce (contents m) (contents a) =
    contents (⟨ValArith.mulF m.val a.val⟩ : Quantity Dim.force α) := by
  simp [newtonForce]

-- ============================================================================
-- Part 2: Momentum — p = mv
-- ============================================================================

def momentum [ValArith α]
    (mass : Val (Quantity Dim.M α))
    (vel : Val (Quantity Dim.velocity α)) :
    Val (Quantity Dim.momentum α) :=
  mulQ mass vel

theorem momentum_mass_origin [ValArith α]
    (vel : Val (Quantity Dim.velocity α)) :
    momentum (origin : Val (Quantity Dim.M α)) vel = origin := by
  simp [momentum]

theorem momentum_vel_origin [ValArith α]
    (mass : Val (Quantity Dim.M α)) :
    momentum mass (origin : Val (Quantity Dim.velocity α)) = origin := by
  simp [momentum]

theorem momentum_contents [ValArith α]
    (m : Quantity Dim.M α) (v : Quantity Dim.velocity α) :
    momentum (contents m) (contents v) =
    contents (⟨ValArith.mulF m.val v.val⟩ : Quantity Dim.momentum α) := by
  simp [momentum]

-- ============================================================================
-- Part 3: Kinetic Energy — T = mv²
-- ============================================================================

-- The ½ is a scalar constant; omitted for structural clarity.
-- Dimensions: mass × velocity × velocity = ⟨1,0,0⟩ + ⟨0,1,-1⟩ + ⟨0,1,-1⟩ = ⟨1,2,-2⟩ = energy.

def kineticEnergy [ValArith α]
    (mass : Val (Quantity Dim.M α))
    (vel : Val (Quantity Dim.velocity α)) :
    Val (Quantity Dim.energy α) :=
  mulQ mass (mulQ vel vel)

/-- Mass at singularity: no kinetic energy. -/
theorem kinetic_mass_origin [ValArith α]
    (vel : Val (Quantity Dim.velocity α)) :
    kineticEnergy (origin : Val (Quantity Dim.M α)) vel = origin := by
  simp [kineticEnergy]

/-- Velocity at singularity: no kinetic energy. -/
theorem kinetic_vel_origin [ValArith α]
    (mass : Val (Quantity Dim.M α)) :
    kineticEnergy mass (origin : Val (Quantity Dim.velocity α)) = origin := by
  cases mass <;> simp [kineticEnergy, mulQ, liftBin₂]

/-- Both defined: computes. -/
theorem kinetic_contents [ValArith α]
    (m : Quantity Dim.M α) (v : Quantity Dim.velocity α) :
    kineticEnergy (contents m) (contents v) =
    contents (⟨ValArith.mulF m.val (ValArith.mulF v.val v.val)⟩ : Quantity Dim.energy α) := by
  simp [kineticEnergy]

-- ============================================================================
-- Part 4: Gravitational Potential — V = -coeff/r
-- ============================================================================

-- coeff = GMm (precomputed). Dimension: energy × length.
-- r has dimension length. coeff/r has dimension energy.
-- At r = origin (singularity): V = origin. No hypothesis.

def gravPotential [ValArith α]
    (coeff : Val (Quantity Dim.potentialCoeff α))
    (r : Val (Quantity Dim.L α)) :
    Val (Quantity Dim.energy α) :=
  neg (divQ coeff r)

/-- Singularity: potential was never in the counting domain. Not infinity. Not undefined. -/
theorem gravPotential_r_origin [ValArith α]
    (coeff : Val (Quantity Dim.potentialCoeff α)) :
    gravPotential coeff (origin : Val (Quantity Dim.L α)) = origin := by
  simp [gravPotential]

/-- Undefined source: potential is origin. -/
theorem gravPotential_coeff_origin [ValArith α]
    (r : Val (Quantity Dim.L α)) :
    gravPotential (origin : Val (Quantity Dim.potentialCoeff α)) r = origin := by
  simp [gravPotential]

/-- Both defined: computes. -/
theorem gravPotential_contents [ValArith α]
    (c : Quantity Dim.potentialCoeff α) (r : Quantity Dim.L α) :
    gravPotential (contents c) (contents r) ≠ origin := by
  simp [gravPotential, divQ, liftBin₂, neg]

-- ============================================================================
-- Part 5: Total Energy — E = T + V
-- ============================================================================

-- Both terms have dimension energy. Same-dimension addition.
-- Val handles existence: if either term is origin, total is origin.

def totalEnergy [ValArith α]
    (kinetic potential : Val (Quantity Dim.energy α)) :
    Val (Quantity Dim.energy α) :=
  add kinetic potential

theorem totalEnergy_kinetic_origin [ValArith α]
    (potential : Val (Quantity Dim.energy α)) :
    totalEnergy origin potential = origin := by
  simp [totalEnergy]

theorem totalEnergy_potential_origin [ValArith α]
    (kinetic : Val (Quantity Dim.energy α)) :
    totalEnergy kinetic origin = origin := by
  simp [totalEnergy]

theorem totalEnergy_contents [ValArith α]
    (t v : Quantity Dim.energy α) :
    totalEnergy (contents t) (contents v) =
    contents (⟨ValArith.addF t.val v.val⟩ : Quantity Dim.energy α) := rfl

-- ============================================================================
-- Part 6: Work-Energy Theorem — W = T₂ - T₁
-- ============================================================================

def work [ValArith α]
    (t₁ t₂ : Val (Quantity Dim.energy α)) :
    Val (Quantity Dim.energy α) :=
  add t₂ (neg t₁)

/-- Work from a singularity state: origin. -/
theorem work_from_origin [ValArith α]
    (t₂ : Val (Quantity Dim.energy α)) :
    work origin t₂ = origin := by
  cases t₂ <;> simp [work, add, neg]

/-- Work to a singularity state: origin. -/
theorem work_to_origin [ValArith α]
    (t₁ : Val (Quantity Dim.energy α)) :
    work t₁ origin = origin := by
  simp [work]

-- ============================================================================
-- Part 7: Two-Body Gravitational System — Multiple Existence Boundaries
-- ============================================================================

-- Two bodies: V_total = V₁(r₁) + V₂(r₂).
-- If either distance is at a singularity, the total potential is origin.
-- Standard: h₁ : r₁ ≠ 0, h₂ : r₂ ≠ 0. Val: zero hypotheses.

def twoBodyPotential [ValArith α]
    (c₁ c₂ : Val (Quantity Dim.potentialCoeff α))
    (r₁ r₂ : Val (Quantity Dim.L α)) :
    Val (Quantity Dim.energy α) :=
  add (gravPotential c₁ r₁) (gravPotential c₂ r₂)

/-- First body at singularity: total potential is origin. -/
theorem twoBody_r1_origin [ValArith α]
    (c₁ c₂ : Val (Quantity Dim.potentialCoeff α))
    (r₂ : Val (Quantity Dim.L α)) :
    twoBodyPotential c₁ c₂ origin r₂ = origin := by
  simp [twoBodyPotential, gravPotential]

/-- Second body at singularity: total potential is origin. -/
theorem twoBody_r2_origin [ValArith α]
    (c₁ c₂ : Val (Quantity Dim.potentialCoeff α))
    (r₁ : Val (Quantity Dim.L α)) :
    twoBodyPotential c₁ c₂ r₁ origin = origin := by
  simp [twoBodyPotential, gravPotential]

-- ============================================================================
-- Part 8: Comparison — Standard vs Val
-- ============================================================================

-- STANDARD APPROACH:
--
--   def force (m a : ℝ) : ℝ := m * a
--   -- No dimensional checking. force 3.0 "hello" would typecheck in ℝ.
--   -- No existence boundary handling.
--
--   theorem gravPotential (k r : ℝ) (hr : r ≠ 0) : V = k / r := ...
--   -- hr threaded through every caller.
--
--   theorem twoBody (k₁ k₂ r₁ r₂ : ℝ) (hr₁ : r₁ ≠ 0) (hr₂ : r₂ ≠ 0) :
--       V_total = k₁/r₁ + k₂/r₂ := ...
--   -- Two hypotheses threaded.

-- VAL + LEAN TYPE SYSTEM:
--
--   def newtonForce (mass : Val (Quantity Dim.M α)) (accel : Val (Quantity Dim.acceleration α)) :
--       Val (Quantity Dim.force α) := mulQ mass accel
--   -- Dimensional consistency: Lean's type system. No hypothesis.
--   -- Existence boundary: Val's sort dispatch. No hypothesis.
--
--   theorem twoBody_r1_origin ... := by cases <;> simp
--   -- Zero hypotheses. Two mechanisms. Each doing what it's best at.

-- ============================================================================
-- Part 9: The Verdict
-- ============================================================================

-- DOES THE PHYSICS LAYER WORK WITH BOTH MECHANISMS?
--
-- Yes. Count the hypotheses:
--
--   Theorem                         Standard    Val + Types
--   ─────────────────────────────────────────────────────────
--   newton_mass_origin              n/a         0
--   newton_accel_origin             n/a         0
--   newton_contents                 0           0
--   momentum_mass_origin            n/a         0
--   momentum_vel_origin             n/a         0
--   kinetic_mass_origin             hm > 0      0
--   kinetic_vel_origin              n/a         0
--   gravPotential_r_origin          hr ≠ 0      0
--   gravPotential_coeff_origin      n/a         0
--   totalEnergy_kinetic_origin      n/a         0
--   totalEnergy_potential_origin    n/a         0
--   work_from_origin                h₁          0
--   work_to_origin                  h₂          0
--   twoBody_r1_origin               hr₁ ≠ 0    0
--   twoBody_r2_origin               hr₂ ≠ 0    0
--   ─────────────────────────────────────────────
--   Dimensional consistency:         0 (no checking)  0 (type system)
--   Existence boundary:              5 hypotheses     0 hypotheses
--
-- The same dissolution as PointCharge and Vacuum, now with dimensional
-- typing on top. Two mechanisms, one domain file, zero hypotheses.

end Val
