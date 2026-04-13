/-
Released under MIT license.
-/
import Val.Physics.Dimension

/-!
# Val Physics: Electromagnetism

Extends PointCharge.lean into a full domain file. Maxwell's equations,
Lorentz force, electromagnetic energy density, and the magnetic monopole
question.

## The Honest Boundary

Val handles:
- Field singularities — where E or B is undefined (origin, not zero)
- Multi-field composition — E² + B² with independent boundaries
- The monopole assumption — div B = 0 carried structurally by the sort

Val does NOT handle:
- Differential structure — curl, divergence, exterior derivative
- Wave equation solutions — propagation, boundary conditions
- Radiation — Larmor formula, antenna patterns
- Quantum corrections — vacuum polarization, running coupling
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Part 1: Coulomb's Law (extends PointCharge, now dimensioned)
-- ============================================================================

-- F = coeff/r² where coeff = kq₁q₂ (precomputed).
-- Dimension: potentialCoeff / area = force
-- ⟨1,3,-2,0,0⟩ / ⟨0,2,0,0,0⟩ = ⟨1,1,-2,0,0⟩ = force ✓

def coulombForce [ValArith α]
    (coeff : Val (Quantity Dim.potentialCoeff α))
    (r : Val (Quantity Dim.L α)) :
    Val (Quantity Dim.force α) :=
  divQ coeff (mulQ r r)

/-- Singularity: force concept doesn't apply here. No h : r ≠ 0. -/
theorem coulomb_r_origin [ValArith α]
    (coeff : Val (Quantity Dim.potentialCoeff α)) :
    coulombForce coeff (origin : Val (Quantity Dim.L α)) = origin := by
  simp [coulombForce]

/-- No charge (coeff = origin): no force. -/
theorem coulomb_coeff_origin [ValArith α]
    (r : Val (Quantity Dim.L α)) :
    coulombForce (origin : Val (Quantity Dim.potentialCoeff α)) r = origin := by
  simp [coulombForce]

/-- Both defined: computes. -/
theorem coulomb_contents_ne_origin [ValArith α]
    (c : Quantity Dim.potentialCoeff α) (r : Quantity Dim.L α) :
    coulombForce (contents c) (contents r) ≠ origin := by
  simp [coulombForce, divQ, mulQ, liftBin₂]

-- ============================================================================
-- Part 2: Lorentz Force — F = qE + qv × B
-- ============================================================================

-- Electric contribution: F_E = q * E
-- charge × electricField = force ✓

def lorentzElectric [ValArith α]
    (q : Val (Quantity Dim.charge α))
    (e : Val (Quantity Dim.electricField α)) :
    Val (Quantity Dim.force α) :=
  mulQ q e

-- Magnetic contribution: F_B = q * v × B
-- charge × velocity × magneticField = force ✓

def lorentzMagnetic [ValArith α]
    (q : Val (Quantity Dim.charge α))
    (v : Val (Quantity Dim.velocity α))
    (b : Val (Quantity Dim.magneticField α)) :
    Val (Quantity Dim.force α) :=
  mulQ (mulQ q v) b

-- Total Lorentz force: both terms have dimension force, so add works.

def lorentzForce [ValArith α]
    (q : Val (Quantity Dim.charge α))
    (e : Val (Quantity Dim.electricField α))
    (v : Val (Quantity Dim.velocity α))
    (b : Val (Quantity Dim.magneticField α)) :
    Val (Quantity Dim.force α) :=
  add (lorentzElectric q e) (lorentzMagnetic q v b)

/-- No charge: no Lorentz force. Regardless of fields. -/
theorem lorentz_q_origin [ValArith α]
    (e : Val (Quantity Dim.electricField α))
    (v : Val (Quantity Dim.velocity α))
    (b : Val (Quantity Dim.magneticField α)) :
    lorentzForce origin e v b = origin := by
  simp [lorentzForce, lorentzElectric, lorentzMagnetic, add, mulQ, liftBin₂]

/-- E field at singularity, no B: electric contribution origin. -/
theorem lorentz_e_origin [ValArith α]
    (q : Val (Quantity Dim.charge α)) :
    lorentzElectric q (origin : Val (Quantity Dim.electricField α)) = origin := by
  simp [lorentzElectric]

/-- B field at singularity: magnetic contribution origin. -/
theorem lorentz_b_origin [ValArith α]
    (q : Val (Quantity Dim.charge α))
    (v : Val (Quantity Dim.velocity α)) :
    lorentzMagnetic q v (origin : Val (Quantity Dim.magneticField α)) = origin := by
  cases q <;> cases v <;> simp [lorentzMagnetic, mulQ, liftBin₂]

-- ============================================================================
-- Part 3: Electromagnetic Energy Density — u = ε₀E² + B²/μ₀
-- ============================================================================

-- Two independent field contributions. If either field is at a singularity,
-- its contribution is origin. The two-field composition shows the N-boundary
-- pattern: each field handles its own existence boundary independently.

-- Electric contribution: u_E = ε₀ * E * E
-- permittivity × electricField² = energyDensity ✓

def electricEnergyDensity [ValArith α]
    (eps : Val (Quantity Dim.permittivity α))
    (e : Val (Quantity Dim.electricField α)) :
    Val (Quantity Dim.energyDensity α) :=
  mulQ eps (mulQ e e)

-- Magnetic contribution: u_B = (1/μ₀) * B * B
-- invPermeability × magneticField² = energyDensity ✓

def magneticEnergyDensity [ValArith α]
    (invMu : Val (Quantity Dim.invPermeability α))
    (b : Val (Quantity Dim.magneticField α)) :
    Val (Quantity Dim.energyDensity α) :=
  mulQ invMu (mulQ b b)

-- Total: u = u_E + u_B

def emEnergyDensity [ValArith α]
    (eps : Val (Quantity Dim.permittivity α))
    (invMu : Val (Quantity Dim.invPermeability α))
    (e : Val (Quantity Dim.electricField α))
    (b : Val (Quantity Dim.magneticField α)) :
    Val (Quantity Dim.energyDensity α) :=
  add (electricEnergyDensity eps e) (magneticEnergyDensity invMu b)

/-- E not in counting domain: neither is electric energy density. -/
theorem eEnergy_e_origin [ValArith α]
    (eps : Val (Quantity Dim.permittivity α)) :
    electricEnergyDensity eps (origin : Val (Quantity Dim.electricField α)) = origin := by
  cases eps <;> simp [electricEnergyDensity, mulQ, liftBin₂]

/-- B not in counting domain: neither is magnetic energy density. -/
theorem bEnergy_b_origin [ValArith α]
    (invMu : Val (Quantity Dim.invPermeability α)) :
    magneticEnergyDensity invMu (origin : Val (Quantity Dim.magneticField α)) = origin := by
  cases invMu <;> simp [magneticEnergyDensity, mulQ, liftBin₂]

/-- E not in counting domain: total energy density not in counting domain. -/
theorem emEnergy_e_origin [ValArith α]
    (eps : Val (Quantity Dim.permittivity α))
    (invMu : Val (Quantity Dim.invPermeability α))
    (b : Val (Quantity Dim.magneticField α)) :
    emEnergyDensity eps invMu origin b = origin := by
  simp [emEnergyDensity, electricEnergyDensity, eEnergy_e_origin, add]

/-- B not in counting domain: total energy density not in counting domain. -/
theorem emEnergy_b_origin [ValArith α]
    (eps : Val (Quantity Dim.permittivity α))
    (invMu : Val (Quantity Dim.invPermeability α))
    (e : Val (Quantity Dim.electricField α)) :
    emEnergyDensity eps invMu e origin = origin := by
  simp [emEnergyDensity, magneticEnergyDensity, bEnergy_b_origin, add]
  cases e <;> cases eps <;> simp [electricEnergyDensity, mulQ, liftBin₂, add]

-- ============================================================================
-- Part 4: Magnetic Monopole — div B = 0
-- ============================================================================

-- In standard physics: div B = 0 everywhere. No magnetic charges.
-- In Val: the magnetic charge density is always origin.
-- Not zero charge density (contents(0)). No charge to speak of (origin).
-- If monopoles existed, this could be contents. The sort carries the assumption.

def magneticChargeDensity [ValArith α] : Val (Quantity Dim.charge α) :=
  origin

/-- No magnetic monopoles: charge density is origin. Structural. -/
theorem no_monopole [ValArith α] :
    (magneticChargeDensity : Val (Quantity Dim.charge α)) = origin := rfl

/-- The force from a magnetic charge is origin. Always. -/
theorem monopole_force [ValArith α]
    (r : Val (Quantity Dim.L α)) :
    coulombForce (origin : Val (Quantity Dim.potentialCoeff α)) r = origin := by
  simp [coulombForce]

-- ============================================================================
-- Part 5: Two-Source System — Independent Singularities
-- ============================================================================

-- Two charges at different positions. Each may be at a singularity.
-- Standard: h₁ : r₁ ≠ 0, h₂ : r₂ ≠ 0. Val: zero hypotheses.

def twoChargeForce [ValArith α]
    (c₁ c₂ : Val (Quantity Dim.potentialCoeff α))
    (r₁ r₂ : Val (Quantity Dim.L α)) :
    Val (Quantity Dim.force α) :=
  add (coulombForce c₁ r₁) (coulombForce c₂ r₂)

/-- First charge at singularity: total force origin. -/
theorem twoCharge_r1_origin [ValArith α]
    (c₁ c₂ : Val (Quantity Dim.potentialCoeff α))
    (r₂ : Val (Quantity Dim.L α)) :
    twoChargeForce c₁ c₂ origin r₂ = origin := by
  simp [twoChargeForce, coulombForce]

/-- Second charge at singularity: total force origin. -/
theorem twoCharge_r2_origin [ValArith α]
    (c₁ c₂ : Val (Quantity Dim.potentialCoeff α))
    (r₁ : Val (Quantity Dim.L α)) :
    twoChargeForce c₁ c₂ r₁ origin = origin := by
  simp [twoChargeForce, coulombForce]

-- ============================================================================
-- Part 6: Electric Potential — V = coeff/r
-- ============================================================================

-- Dimension: potentialCoeff / length = energy ✓

def electricPotential [ValArith α]
    (coeff : Val (Quantity Dim.potentialCoeff α))
    (r : Val (Quantity Dim.L α)) :
    Val (Quantity Dim.energy α) :=
  divQ coeff r

/-- Singularity: potential concept doesn't apply. -/
theorem potential_r_origin [ValArith α]
    (coeff : Val (Quantity Dim.potentialCoeff α)) :
    electricPotential coeff (origin : Val (Quantity Dim.L α)) = origin := by
  simp [electricPotential]

-- ============================================================================
-- Part 7: Comparison — Standard vs Val
-- ============================================================================

-- STANDARD APPROACH:
--
--   theorem coulomb (k q₁ q₂ r : ℝ) (hr : r ≠ 0) : F = kq₁q₂/r² := ...
--   theorem lorentz (q E v B : ℝ) : F = qE + qvB := ...
--   -- No h needed for Lorentz since no division.
--   -- But h : q ≠ 0 needed for non-trivial results in practice.
--   theorem energy_density (ε₀ E μ₀ B : ℝ) (hε : ε₀ > 0) (hμ : μ₀ > 0) :
--       u = ε₀E²/2 + B²/(2μ₀) := ...
--   theorem two_charge (k q₁ q₂ r₁ r₂ : ℝ) (h₁ : r₁ ≠ 0) (h₂ : r₂ ≠ 0) :
--       F = F₁ + F₂ := ...
--   theorem potential (k q r : ℝ) (hr : r ≠ 0) : V = kq/r := ...

-- ============================================================================
-- Part 8: The Verdict
-- ============================================================================

-- DOES ORIGIN HANDLE ELECTROMAGNETIC EXISTENCE BOUNDARIES?
--
-- Yes. Hypothesis count:
--
--   Theorem                         Standard         Val
--   ─────────────────────────────────────────────────────────
--   coulomb_r_origin                hr : r ≠ 0       0
--   coulomb_coeff_origin            n/a              0
--   lorentz_q_origin                n/a              0
--   lorentz_e_origin                n/a              0
--   lorentz_b_origin                n/a              0
--   eEnergy_e_origin                n/a              0
--   bEnergy_b_origin                n/a              0
--   emEnergy_e_origin               hε > 0           0
--   emEnergy_b_origin               hμ > 0           0
--   twoCharge_r1_origin             h₁ : r₁ ≠ 0     0
--   twoCharge_r2_origin             h₂ : r₂ ≠ 0     0
--   potential_r_origin              hr : r ≠ 0       0
--   ─────────────────────────────────────────────
--   Existence hypotheses dissolved:  6
--
-- The monopole result is structural, not a dissolved hypothesis.
-- div B = 0 is an assumption, not a boundary guard. In Val it's
-- carried by the sort: magneticChargeDensity = origin, by construction.
--
-- Running total:
--   PointCharge:        14
--   Vacuum:             17
--   Classical:           5
--   Thermodynamics:      9
--   Electromagnetism:    6
--   ─────────────────────
--   Total:              51 existence hypotheses dissolved

end Val
