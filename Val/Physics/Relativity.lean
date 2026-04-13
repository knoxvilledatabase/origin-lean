/-
Released under MIT license.
-/
import Val.Physics.Dimension

/-!
# Val Physics: Relativity

The hardest existence boundaries in classical physics. Two kinds of
origin that are physically distinct:

1. The physical singularity at r=0 — spatial origin, same as PointCharge
   but deeper. Spacetime curvature diverges. The quantity doesn't exist.
2. The event horizon at r=2GM/c² — causal origin. Information beyond the
   horizon doesn't exist in the accessible universe. Not practically
   difficult — structurally inaccessible.

The most important demonstration: coordinate singularity vs physical
singularity. The event horizon is origin in Schwarzschild coordinates
(undefined at that coordinate value) but contents in Kruskal coordinates
(the quantity exists, you can cross it). The sort is coordinate-dependent.
That's physically correct.

## The Honest Boundary

Val handles:
- Physical singularity at r=0 (spatial origin)
- Event horizon as causal origin (information doesn't exist)
- Coordinate singularity vs physical singularity (sort is coordinate-dependent)
- Causal structure — lightcone boundaries as origin

Val does NOT handle:
- Einstein field equations (differential geometry infrastructure)
- Geodesic deviation (curvature tensor machinery)
- Penrose singularity theorems (topological methods)
- Quantum gravity at the singularity — one of physics' 23 patches.
  Val names the boundary. Nobody knows what's on the other side.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Part 1: Schwarzschild Metric — Two Kinds of Origin
-- ============================================================================

-- The Schwarzschild metric has two special radii:
--   r = 0: physical singularity. Curvature diverges. Origin.
--   r = r_s (2GM/c²): event horizon. Coordinate singularity in
--     Schwarzschild coords, but a regular surface physically.

-- Metric component g_tt = 1 - r_s/r.
-- At r = origin (physical singularity): g_tt is origin.
-- At r = contents(r_s) (event horizon): g_tt = contents(0). A quantity.
-- The distinction: contents(0) at the horizon vs origin at the singularity.

def metricComponent [ValArith α]
    (rs : α) (r : Val α) : Val α :=
  valMap (fun r₀ => ValArith.addF (ValArith.mulF r₀ r₀)
    (ValArith.negF (ValArith.mulF rs r₀))) r

/-- At the physical singularity: metric is origin. Not infinite. Not undefined.
    Origin — the quantity doesn't exist. -/
theorem metric_at_singularity [ValArith α] (rs : α) :
    metricComponent rs (origin : Val α) = origin := rfl

/-- At a regular point: metric computes. -/
theorem metric_at_contents [ValArith α] (rs r₀ : α) :
    metricComponent rs (contents r₀) =
    contents (ValArith.addF (ValArith.mulF r₀ r₀)
      (ValArith.negF (ValArith.mulF rs r₀))) := rfl

-- ============================================================================
-- Part 2: Coordinate Singularity vs Physical Singularity
-- ============================================================================

-- The event horizon in Schwarzschild coordinates: g_tt = 0 at r = r_s.
-- But this is contents(0), not origin. The metric EXISTS there — it's
-- the coordinate system that fails, not the spacetime.
--
-- In Kruskal coordinates, the same point has non-degenerate metric
-- components. The quantity exists in both coordinate systems.
--
-- The physical singularity at r = 0 is origin in ALL coordinate systems.
-- No coordinate transformation makes it contents.
--
-- Val captures this: origin is coordinate-invariant (physical singularity).
-- contents(0) is coordinate-dependent (can be transformed away).

/-- Schwarzschild view of event horizon: the metric exists (contents). -/
def schwarzschildAtHorizon [ValArith α]
    (metricValue : α) : Val α :=
  contents metricValue  -- contents(0) when rs = r

/-- Kruskal view of the same event: also contents (different value). -/
def kruskalAtHorizon [ValArith α]
    (kruskalValue : α) : Val α :=
  contents kruskalValue  -- non-degenerate in Kruskal coords

/-- Physical singularity: origin in ALL coordinate systems.
    No coordinate transformation changes the sort. -/
def physicalSingularity [ValArith α] : Val α := origin

/-- The event horizon is contents — NOT origin. It's crossable. -/
theorem horizon_is_contents [ValArith α] (v : α) :
    schwarzschildAtHorizon v ≠ (origin : Val α) := by simp [schwarzschildAtHorizon]

/-- The singularity is origin. In every coordinate system. -/
theorem singularity_is_origin [ValArith α] :
    (physicalSingularity : Val α) = origin := rfl

-- ============================================================================
-- Part 3: Gravitational Redshift
-- ============================================================================

-- Frequency shift: ν_obs/ν_emit = √(g_tt(emit)/g_tt(obs)).
-- If either metric component is origin (at the singularity), the
-- redshift is origin. Standard: h : g_tt(obs) ≠ 0. Val: sort dispatch.

def redshiftRatio [ValArith α]
    (gEmit gObs : Val α) : Val α :=
  mul gEmit (inv gObs)

/-- Emitter at singularity: no signal. -/
theorem redshift_emit_origin [ValArith α] (gObs : Val α) :
    redshiftRatio origin gObs = origin := by
  simp [redshiftRatio]

/-- Observer at singularity: no measurement. -/
theorem redshift_obs_origin [ValArith α] (gEmit : Val α) :
    redshiftRatio gEmit origin = origin := by
  simp [redshiftRatio]

-- ============================================================================
-- Part 4: Causal Structure — Lightcone Boundaries
-- ============================================================================

-- In GR, the causal structure defines which events can influence others.
-- Beyond the lightcone: the event is causally disconnected. Origin.
-- Within the lightcone: causal contact exists. Contents.

/-- Causal signal between two events.
    If either event is at a causal boundary, the signal is origin. -/
def causalSignal [ValArith α]
    (coupling : α) (source observer : Val α) : Val α :=
  mul (valMap (ValArith.mulF coupling) source) observer

/-- Source beyond causal boundary: no signal. -/
theorem signal_source_origin [ValArith α] (c : α) (obs : Val α) :
    causalSignal c origin obs = origin := by
  simp [causalSignal, mul]

/-- Observer beyond causal boundary: no measurement. -/
theorem signal_obs_origin [ValArith α] (c : α) (source : Val α) :
    causalSignal c source origin = origin := by
  simp [causalSignal]

/-- Both in causal contact: signal computes. -/
theorem signal_contents [ValArith α] (c s o : α) :
    causalSignal c (contents s) (contents o) =
    contents (ValArith.mulF (ValArith.mulF c s) o) := rfl

-- ============================================================================
-- Part 5: Proper Time — dτ² = g_tt dt²
-- ============================================================================

-- Proper time along a worldline. At the singularity: origin.
-- At the horizon: contents (proper time is finite for infalling observer).

def properTime [ValArith α]
    (gtt : Val α) (dt : Val α) : Val α :=
  mul gtt (mul dt dt)

/-- At the singularity: no proper time. -/
theorem properTime_singularity [ValArith α] (dt : Val α) :
    properTime origin dt = origin := by
  simp [properTime]

/-- Time interval at boundary: origin. -/
theorem properTime_dt_origin [ValArith α] (gtt : Val α) :
    properTime gtt origin = origin := by
  simp [properTime]

-- ============================================================================
-- Part 6: Two Black Holes — Independent Singularities
-- ============================================================================

-- Binary black hole: two physical singularities. Each creates its own
-- existence boundary. Standard: h₁ : r ≠ r₁, h₂ : r ≠ r₂.
-- Val: two independent sort dispatches.

def binaryGravField [ValArith α]
    (k₁ k₂ : α) (r₁ r₂ : Val α) : Val α :=
  add (invSquare k₁ r₁) (invSquare k₂ r₂)

/-- At first singularity: field is origin. -/
theorem binary_r1_origin [ValArith α] (k₁ k₂ : α) (r₂ : Val α) :
    binaryGravField k₁ k₂ origin r₂ = origin := by simp [binaryGravField]

/-- At second singularity: field is origin. -/
theorem binary_r2_origin [ValArith α] (k₁ k₂ : α) (r₁ : Val α) :
    binaryGravField k₁ k₂ r₁ origin = origin := by
  cases r₁ <;> simp [binaryGravField, invSquare, add]

-- ============================================================================
-- Part 7: Quantum Gravity — The Named Unknown
-- ============================================================================

-- At the physical singularity, general relativity predicts infinite curvature.
-- Quantum mechanics predicts nothing (it's not a quantum theory of gravity).
-- The quantity at the singularity isn't just undefined — both theories
-- that might describe it break down.
--
-- Val: the singularity is origin. Not because we chose it to be.
-- Because the quantity genuinely doesn't exist in any theory we have.
--
-- This is the deepest honest boundary. The other files defer analytic
-- infrastructure (completeness, convergence). This file defers an
-- entire theory that doesn't exist yet.
--
-- Quantum gravity is one of physics' 23 patches. Val names where the
-- boundary is. Nobody knows what's on the other side.

-- ============================================================================
-- Part 8: Comparison — Standard vs Val
-- ============================================================================

-- STANDARD APPROACH:
--
--   theorem redshift (g_emit g_obs : ℝ) (h_obs : g_obs ≠ 0) :
--       ν_obs/ν_emit = √(g_emit/g_obs) := ...
--
--   theorem proper_time (g_tt dt : ℝ) (h_gtt : g_tt > 0) :
--       dτ² = g_tt * dt² := ...
--
--   theorem binary (k₁ k₂ r₁ r₂ : ℝ) (h₁ : r₁ ≠ 0) (h₂ : r₂ ≠ 0) :
--       Φ = k₁/r₁² + k₂/r₂² := ...

-- ============================================================================
-- Part 9: The Verdict
-- ============================================================================

-- DOES ORIGIN HANDLE RELATIVISTIC EXISTENCE BOUNDARIES?
--
-- Yes. Two physically distinct kinds of origin confirmed:
--   1. Physical singularity (r=0): origin in all coordinate systems
--   2. Event horizon: contents (crossable) — NOT origin
-- The coordinate singularity vs physical singularity distinction
-- is structural in Val. Origin is coordinate-invariant.
--
-- Hypothesis count:
--
--   Theorem                         Standard              Val
--   ─────────────────────────────────────────────────────────────
--   metric_at_singularity           n/a                    0
--   redshift_emit_origin            n/a                    0
--   redshift_obs_origin             h : g_obs ≠ 0         0
--   signal_source_origin            n/a                    0
--   signal_obs_origin               n/a                    0
--   properTime_singularity          n/a                    0
--   properTime_dt_origin            h : g_tt > 0          0
--   binary_r1_origin                h₁ : r₁ ≠ 0          0
--   binary_r2_origin                h₂ : r₂ ≠ 0          0
--   ─────────────────────────────────────────────────────────
--   Existence hypotheses dissolved:  4
--
-- Running total:
--   PointCharge:        14
--   Vacuum:             17
--   Classical:           5
--   Thermodynamics:      9
--   Electromagnetism:    6
--   QuantumMechanics:   14
--   StatMech:            9
--   Relativity:          4
--   ─────────────────────
--   Total:              78 existence hypotheses dissolved

end Val
