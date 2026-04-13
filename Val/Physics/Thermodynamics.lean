/-
Released under MIT license.
-/
import Val.Physics.Dimension

/-!
# Val Physics: Thermodynamics

The second domain file. Tests a new kind of existence boundary:
absolute zero and non-equilibrium states.

Singularities are spatial (r = 0, field doesn't exist).
Vacuum is particle-counting (no particles to count).
Absolute zero is thermal (thermodynamic temperature doesn't apply).

If origin handles all three through the same sort dispatch,
that's the third confirmation that origin captures existence boundaries
as a concept, not just one application.

## The Honest Boundary

Val handles:
- Absolute zero as origin (not contents(0) — the third law)
- Non-equilibrium states as origin (state functions undefined)
- Singularities in thermodynamic quantities (T in denominator)

Val does NOT handle:
- PDE existence for non-equilibrium systems
- Statistical mechanics derivations of thermodynamic laws
- Phase transition critical exponents
- Fluctuation-dissipation relations
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Part 1: Thermodynamic State
-- ============================================================================

-- Temperature as Val (Quantity Dim.temperature α):
--   origin    = absolute zero boundary / non-equilibrium. Temperature doesn't apply.
--   contents  = equilibrium. Temperature is defined and measurable.
--   container = system was in equilibrium, last known temperature preserved.
--
-- contents(0) would mean "we measured zero kelvin." The third law says you can't.
-- origin means "thermodynamic temperature doesn't apply here."

-- ============================================================================
-- Part 2: Heat Transfer — Q = mcΔT
-- ============================================================================

-- Dimensions: mass × specificHeat × temperature = energy
-- ⟨1,0,0,0⟩ + ⟨0,2,-2,-1⟩ + ⟨0,0,0,1⟩ = ⟨1,2,-2,0⟩ = energy ✓

def heatTransfer [ValArith α]
    (mass : Val (Quantity Dim.M α))
    (cp : Val (Quantity Dim.specificHeat α))
    (deltaT : Val (Quantity Dim.temperature α)) :
    Val (Quantity Dim.energy α) :=
  mulQ mass (mulQ cp deltaT)

/-- No mass (singularity): no heat transfer. -/
theorem heat_mass_origin [ValArith α]
    (cp : Val (Quantity Dim.specificHeat α))
    (deltaT : Val (Quantity Dim.temperature α)) :
    heatTransfer (origin : Val (Quantity Dim.M α)) cp deltaT = origin := by
  simp [heatTransfer]

/-- At absolute zero boundary (ΔT = origin): no heat transfer. -/
theorem heat_temp_origin [ValArith α]
    (mass : Val (Quantity Dim.M α))
    (cp : Val (Quantity Dim.specificHeat α)) :
    heatTransfer mass cp (origin : Val (Quantity Dim.temperature α)) = origin := by
  cases mass <;> cases cp <;> simp [heatTransfer, mulQ, liftBin₂]

/-- All defined: computes. -/
theorem heat_contents [ValArith α]
    (m : Quantity Dim.M α) (cp : Quantity Dim.specificHeat α)
    (dT : Quantity Dim.temperature α) :
    heatTransfer (contents m) (contents cp) (contents dT) =
    contents (⟨ValArith.mulF m.val (ValArith.mulF cp.val dT.val)⟩ :
      Quantity Dim.energy α) := by
  simp [heatTransfer]

-- ============================================================================
-- Part 3: Entropy — dS = dQ/T
-- ============================================================================

-- Standard: requires h : T ≠ 0 or h : T > 0.
-- Val: if T is origin, entropy change is origin. No hypothesis.

def entropyChange [ValArith α]
    (dQ : Val (Quantity Dim.energy α))
    (temp : Val (Quantity Dim.temperature α)) :
    Val (Quantity Dim.entropy α) :=
  divQ dQ temp

/-- Entropy at absolute zero boundary: origin. Not zero entropy — no entropy. -/
theorem entropy_at_origin [ValArith α]
    (dQ : Val (Quantity Dim.energy α)) :
    entropyChange dQ (origin : Val (Quantity Dim.temperature α)) = origin := by
  simp [entropyChange]

/-- No heat to account for: origin. -/
theorem entropy_no_heat [ValArith α]
    (temp : Val (Quantity Dim.temperature α)) :
    entropyChange (origin : Val (Quantity Dim.energy α)) temp = origin := by
  simp [entropyChange]

/-- Both defined: computes. -/
theorem entropy_contents [ValArith α]
    (dQ : Quantity Dim.energy α) (temp : Quantity Dim.temperature α) :
    entropyChange (contents dQ) (contents temp) =
    contents (⟨ValArith.mulF dQ.val (ValArith.invF temp.val)⟩ :
      Quantity Dim.entropy α) := by
  simp [entropyChange]

-- ============================================================================
-- Part 4: Carnot Efficiency — η = 1 - T_cold/T_hot
-- ============================================================================

-- Standard: requires h : T_hot > 0.
-- Val: if T_hot is origin, efficiency is origin.

def carnotRatio [ValArith α]
    (tCold tHot : Val (Quantity Dim.temperature α)) :
    Val (Quantity Dim.scalar α) :=
  divQ tCold tHot

/-- Hot reservoir at absolute zero: ratio is origin. -/
theorem carnot_hot_origin [ValArith α]
    (tCold : Val (Quantity Dim.temperature α)) :
    carnotRatio tCold (origin : Val (Quantity Dim.temperature α)) = origin := by
  simp [carnotRatio]

/-- Cold reservoir at absolute zero: ratio is origin. -/
theorem carnot_cold_origin [ValArith α]
    (tHot : Val (Quantity Dim.temperature α)) :
    carnotRatio (origin : Val (Quantity Dim.temperature α)) tHot = origin := by
  simp [carnotRatio]

/-- Both defined: computes. -/
theorem carnot_contents [ValArith α]
    (tC tH : Quantity Dim.temperature α) :
    carnotRatio (contents tC) (contents tH) =
    contents (⟨ValArith.mulF tC.val (ValArith.invF tH.val)⟩ :
      Quantity Dim.scalar α) := by
  simp [carnotRatio]

-- ============================================================================
-- Part 5: Ideal Gas Law — PV = nRT
-- ============================================================================

-- T = PV/(nR). If V is origin (zero-volume singularity), T is origin.
-- nR treated as a combined coefficient with dimension entropy (energy/temperature).

def idealGasTemp [ValArith α]
    (pv : Val (Quantity Dim.energy α))
    (nR : Val (Quantity Dim.entropy α)) :
    Val (Quantity Dim.temperature α) :=
  divQ pv nR

/-- Zero volume → PV = origin → temperature origin. -/
theorem gasTemp_pv_origin [ValArith α]
    (nR : Val (Quantity Dim.entropy α)) :
    idealGasTemp (origin : Val (Quantity Dim.energy α)) nR = origin := by
  simp [idealGasTemp]

/-- No gas (nR = origin): temperature origin. -/
theorem gasTemp_nR_origin [ValArith α]
    (pv : Val (Quantity Dim.energy α)) :
    idealGasTemp pv (origin : Val (Quantity Dim.entropy α)) = origin := by
  simp [idealGasTemp]

-- Pressure from ideal gas: P = nRT/V
def idealGasPressure [ValArith α]
    (nR : Val (Quantity Dim.entropy α))
    (temp : Val (Quantity Dim.temperature α))
    (vol : Val (Quantity Dim.volume α)) :
    Val (Quantity Dim.pressure α) :=
  divQ (mulQ nR temp) vol

/-- Temperature at absolute zero: pressure origin. -/
theorem gasPressure_temp_origin [ValArith α]
    (nR : Val (Quantity Dim.entropy α))
    (vol : Val (Quantity Dim.volume α)) :
    idealGasPressure nR (origin : Val (Quantity Dim.temperature α)) vol = origin := by
  cases nR <;> simp [idealGasPressure, mulQ, divQ, liftBin₂]

/-- Zero volume singularity: pressure origin. -/
theorem gasPressure_vol_origin [ValArith α]
    (nR : Val (Quantity Dim.entropy α))
    (temp : Val (Quantity Dim.temperature α)) :
    idealGasPressure nR temp (origin : Val (Quantity Dim.volume α)) = origin := by
  simp [idealGasPressure]

-- ============================================================================
-- Part 6: First Law — ΔU = Q - W
-- ============================================================================

-- If either heat or work is at an existence boundary, internal energy change is origin.

def firstLaw [ValArith α]
    (heat work_ : Val (Quantity Dim.energy α)) :
    Val (Quantity Dim.energy α) :=
  add heat (neg work_)

/-- Heat undefined: ΔU origin. -/
theorem firstLaw_heat_origin [ValArith α]
    (work_ : Val (Quantity Dim.energy α)) :
    firstLaw origin work_ = origin := by
  simp [firstLaw]

/-- Work undefined: ΔU origin. -/
theorem firstLaw_work_origin [ValArith α]
    (heat : Val (Quantity Dim.energy α)) :
    firstLaw heat origin = origin := by
  cases heat <;> simp [firstLaw, add, neg]

/-- Both defined: computes. -/
theorem firstLaw_contents [ValArith α]
    (q w : Quantity Dim.energy α) :
    firstLaw (contents q) (contents w) =
    contents (⟨ValArith.addF q.val (ValArith.negF w.val)⟩ :
      Quantity Dim.energy α) := rfl

-- ============================================================================
-- Part 7: Thermodynamic Work — W = PΔV
-- ============================================================================

-- Dimensions: pressure × volume = energy
-- ⟨1,-1,-2,0⟩ + ⟨0,3,0,0⟩ = ⟨1,2,-2,0⟩ = energy ✓

def thermoWork [ValArith α]
    (press : Val (Quantity Dim.pressure α))
    (deltaV : Val (Quantity Dim.volume α)) :
    Val (Quantity Dim.energy α) :=
  mulQ press deltaV

/-- Pressure at singularity: no work. -/
theorem work_press_origin [ValArith α]
    (deltaV : Val (Quantity Dim.volume α)) :
    thermoWork (origin : Val (Quantity Dim.pressure α)) deltaV = origin := by
  simp [thermoWork]

/-- Volume at singularity: no work. -/
theorem work_vol_origin [ValArith α]
    (press : Val (Quantity Dim.pressure α)) :
    thermoWork press (origin : Val (Quantity Dim.volume α)) = origin := by
  simp [thermoWork]

-- ============================================================================
-- Part 8: Two-System Heat Exchange
-- ============================================================================

-- Two systems exchanging heat. Each has its own temperature.
-- Standard: h₁ : T₁ > 0, h₂ : T₂ > 0.
-- Val: two independent sort dispatches.

def twoSystemEntropy [ValArith α]
    (dQ₁ dQ₂ : Val (Quantity Dim.energy α))
    (t₁ t₂ : Val (Quantity Dim.temperature α)) :
    Val (Quantity Dim.entropy α) :=
  add (entropyChange dQ₁ t₁) (entropyChange dQ₂ t₂)

/-- First system at absolute zero: total entropy origin. -/
theorem twoSystem_t1_origin [ValArith α]
    (dQ₁ dQ₂ : Val (Quantity Dim.energy α))
    (t₂ : Val (Quantity Dim.temperature α)) :
    twoSystemEntropy dQ₁ dQ₂ origin t₂ = origin := by
  simp [twoSystemEntropy, entropyChange]

/-- Second system at absolute zero: total entropy origin. -/
theorem twoSystem_t2_origin [ValArith α]
    (dQ₁ dQ₂ : Val (Quantity Dim.energy α))
    (t₁ : Val (Quantity Dim.temperature α)) :
    twoSystemEntropy dQ₁ dQ₂ t₁ origin = origin := by
  simp [twoSystemEntropy, entropyChange]

-- ============================================================================
-- Part 9: Heat Capacity — C = dQ/dT
-- ============================================================================

-- Standard: requires h : ΔT ≠ 0.
-- Val: if ΔT is origin, heat capacity is origin.

def heatCapacity [ValArith α]
    (dQ : Val (Quantity Dim.energy α))
    (dT : Val (Quantity Dim.temperature α)) :
    Val (Quantity Dim.entropy α) :=
  divQ dQ dT

/-- At absolute zero boundary: heat capacity origin. -/
theorem heatCap_temp_origin [ValArith α]
    (dQ : Val (Quantity Dim.energy α)) :
    heatCapacity dQ (origin : Val (Quantity Dim.temperature α)) = origin := by
  simp [heatCapacity]

-- ============================================================================
-- Part 10: Comparison — Standard vs Val
-- ============================================================================

-- STANDARD APPROACH:
--
--   theorem entropy_change (dQ T : ℝ) (hT : T > 0) : dS = dQ / T := ...
--   theorem carnot_eff (T_c T_h : ℝ) (hh : T_h > 0) : η = 1 - T_c/T_h := ...
--   theorem ideal_gas (P V n R T : ℝ) (hV : V ≠ 0) : T = PV/(nR) := ...
--   theorem heat_capacity (dQ dT : ℝ) (hdT : dT ≠ 0) : C = dQ/dT := ...
--   theorem two_system (dQ₁ dQ₂ T₁ T₂ : ℝ) (h₁ : T₁ > 0) (h₂ : T₂ > 0) :
--       ΔS = dQ₁/T₁ + dQ₂/T₂ := ...
--
-- Every theorem carries h : T > 0 or h : V ≠ 0.

-- ============================================================================
-- Part 11: The Verdict
-- ============================================================================

-- DOES ORIGIN HANDLE THERMAL EXISTENCE BOUNDARIES?
--
-- Yes. Every theorem in this file has zero existence hypotheses.
--
-- Hypothesis count:
--
--   Theorem                         Standard         Val
--   ─────────────────────────────────────────────────────────
--   heat_mass_origin                n/a              0
--   heat_temp_origin                n/a              0
--   heat_contents                   0                0
--   entropy_at_origin               hT > 0           0
--   entropy_no_heat                 n/a              0
--   entropy_contents                hT > 0           0
--   carnot_hot_origin               hTh > 0          0
--   carnot_cold_origin              n/a              0
--   carnot_contents                 hTh > 0          0
--   gasTemp_pv_origin               n/a              0
--   gasTemp_nR_origin               n/a              0
--   gasPressure_temp_origin         hT > 0           0
--   gasPressure_vol_origin          hV ≠ 0           0
--   firstLaw_heat_origin            n/a              0
--   firstLaw_work_origin            n/a              0
--   work_press_origin               n/a              0
--   work_vol_origin                 n/a              0
--   twoSystem_t1_origin             hT₁ > 0          0
--   twoSystem_t2_origin             hT₂ > 0          0
--   heatCap_temp_origin             hΔT ≠ 0          0
--   ─────────────────────────────────────────────
--   Existence hypotheses dissolved:  9
--
-- Third confirmation. Three physically different existence boundaries:
--   1. Spatial singularity (r = 0)     — PointCharge: 14 dissolved
--   2. Particle vacuum (no particles)  — Vacuum: 17 dissolved
--   3. Thermal boundary (absolute zero) — Thermodynamics: 9 dissolved
--
-- Same constructor. Same sort dispatch. Same proof pattern: cases <;> simp.
-- Origin captures the concept of existence boundary, not just one application.
--
-- Running total: 14 + 17 + 5 + 9 = 45 existence hypotheses dissolved.
-- (5 from Classical.lean)

end Val
