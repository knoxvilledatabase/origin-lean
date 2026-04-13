/-
Released under MIT license.
-/
import Val.Physics.Dimension

/-!
# Val Physics: Field Theory

The deepest existence boundaries in physics. Renormalization,
the Landau pole, and the boundary between bare and renormalized quantities.

## The Honest Boundary

Val handles:
- Unrenormalized quantities as origin (the quantity doesn't exist until
  renormalization specifies a scheme and scale)
- Renormalized quantities as contents(value(μ)) (depend on RG scale)
- Landau pole as origin (the theory breaks down at that energy)
- UV and IR divergences as origin (the integral doesn't exist)

Val does NOT handle:
- Path integral construction
- BPHZ renormalization theorem
- Asymptotic freedom proofs
- The full renormalization group machinery

The renormalization boundary is what Val names. The machinery that
makes renormalization work remains deferred. This is the deepest
honest boundary in the physics layer — the analytic engine that
controls divergences is the hardest piece of mathematical physics.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Part 1: Bare vs Renormalized Quantities
-- ============================================================================

-- In QFT, a "bare" quantity (before renormalization) is formally infinite.
-- It's not a large number. It's origin — the quantity doesn't exist
-- until you specify a renormalization scheme.
--
-- After renormalization at scale μ: contents(value(μ)).
-- The value depends on the scale. The existence is the scheme's gift.

/-- A bare (unrenormalized) quantity. Origin — doesn't exist as a number. -/
def bareQuantity [ValArith α] : Val α := origin

/-- A renormalized quantity at scale μ. Contents — exists. -/
def renormalized [ValArith α] (value : α) : Val α := contents value

/-- Bare quantities are origin. Structural. -/
theorem bare_is_origin [ValArith α] :
    (bareQuantity : Val α) = origin := rfl

/-- Renormalized quantities are contents. -/
theorem renorm_is_contents [ValArith α] (v : α) :
    renormalized v = (contents v : Val α) := rfl

/-- Bare ≠ renormalized. The sort distinguishes them. -/
theorem bare_ne_renorm [ValArith α] (v : α) :
    (bareQuantity : Val α) ≠ renormalized v := by
  simp [bareQuantity, renormalized]

-- ============================================================================
-- Part 2: Renormalized Observables
-- ============================================================================

-- A physical observable computed from renormalized quantities.
-- If any input is bare (origin), the observable is origin.
-- Standard: h : quantity is renormalized. Val: sort dispatch.

def renormObs [ValArith α] (coupling : Val α) (amplitude : Val α) : Val α :=
  mul coupling amplitude

/-- Bare coupling: observable is origin. No h : coupling renormalized. -/
theorem obs_bare_coupling [ValArith α] (amplitude : Val α) :
    renormObs origin amplitude = origin := by
  simp [renormObs]

/-- Bare amplitude: observable is origin. -/
theorem obs_bare_amplitude [ValArith α] (coupling : Val α) :
    renormObs coupling origin = origin := by
  simp [renormObs]

/-- Both renormalized: computes. -/
theorem obs_renorm [ValArith α] (g a : α) :
    renormObs (contents g) (contents a) =
    contents (ValArith.mulF g a) := rfl

-- ============================================================================
-- Part 3: Running Coupling — g(μ)
-- ============================================================================

-- The coupling constant depends on the energy scale μ.
-- At most scales: contents (the coupling exists and has a value).
-- At the Landau pole: origin (the coupling diverges, the theory breaks down).

/-- Running coupling at a given scale. Origin at the Landau pole. -/
def runningCoupling [ValArith α]
    (atLandauPole : Bool) (value : α) : Val α :=
  if atLandauPole then origin else contents value

/-- At the Landau pole: coupling is origin. Not infinity — origin.
    The theory doesn't produce an answer at this energy. -/
theorem coupling_at_landau [ValArith α] (value : α) :
    runningCoupling true value = (origin : Val α) := rfl

/-- Away from the pole: coupling exists. -/
theorem coupling_away [ValArith α] (value : α) :
    runningCoupling false value = contents value := rfl

-- Perturbative expansion with running coupling.
-- If the coupling is at the Landau pole, every term in the expansion is origin.

def perturbativeTerm [ValArith α]
    (coupling : Val α) (matrixElement : Val α) : Val α :=
  mul coupling matrixElement

/-- Coupling at Landau pole: perturbative term origin. -/
theorem perturb_landau [ValArith α] (matrixElement : Val α) :
    perturbativeTerm origin matrixElement = origin := by
  simp [perturbativeTerm]

-- ============================================================================
-- Part 4: UV and IR Divergences
-- ============================================================================

-- A loop integral in QFT. Before regularization: the integral diverges.
-- The divergent integral is origin — not a large number, not infinity,
-- origin. The quantity doesn't exist until regularization + renormalization.

/-- A loop integral: origin if divergent, contents if regulated. -/
def loopIntegral [ValArith α]
    (regulated : Bool) (value : α) : Val α :=
  if regulated then contents value else origin

/-- Unregulated: origin. -/
theorem loop_divergent [ValArith α] (value : α) :
    loopIntegral false value = (origin : Val α) := rfl

/-- Regulated: contents. -/
theorem loop_regulated [ValArith α] (value : α) :
    loopIntegral true value = contents value := rfl

-- An observable built from loop integrals.
-- If any loop integral is divergent (origin), the observable is origin.

def loopObservable [ValArith α]
    (tree : Val α) (oneLoop : Val α) : Val α :=
  add tree oneLoop

/-- Divergent loop: observable origin. No h : integral converges. -/
theorem loopObs_divergent [ValArith α] (tree : Val α) :
    loopObservable tree origin = origin := by
  simp [loopObservable]

/-- Tree-level undefined: observable origin. -/
theorem loopObs_tree_origin [ValArith α] (oneLoop : Val α) :
    loopObservable origin oneLoop = origin := by
  simp [loopObservable]

-- ============================================================================
-- Part 5: Cross Section — The Physical Observable
-- ============================================================================

-- A scattering cross section: the measurable output of QFT.
-- σ = |M|²/F where M is the matrix element and F is the flux.
-- Standard: h : F ≠ 0. Val: if flux is origin, cross section is origin.

def crossSection [ValArith α]
    (matrixElSq flux : Val α) : Val α :=
  mul matrixElSq (inv flux)

/-- Zero flux (vacuum, no beam): cross section origin. No h : F ≠ 0. -/
theorem xsec_flux_origin [ValArith α] (mSq : Val α) :
    crossSection mSq origin = origin := by
  simp [crossSection]

/-- Bare matrix element: cross section origin. -/
theorem xsec_bare [ValArith α] (flux : Val α) :
    crossSection origin flux = origin := by
  simp [crossSection]

/-- Both renormalized: computes. -/
theorem xsec_contents [ValArith α] (m f : α) :
    crossSection (contents m) (contents f) =
    contents (ValArith.mulF m (ValArith.invF f)) := rfl

-- ============================================================================
-- Part 6: Two-Loop — Multiple Divergence Boundaries
-- ============================================================================

-- A two-loop correction: two independent integrals, each potentially divergent.
-- Standard: h₁ : integral₁ converges, h₂ : integral₂ converges.
-- Val: two independent sort dispatches.

def twoLoopCorrection [ValArith α]
    (loop₁ loop₂ : Val α) : Val α :=
  add loop₁ loop₂

/-- First loop divergent: correction origin. -/
theorem twoLoop_first_div [ValArith α] (loop₂ : Val α) :
    twoLoopCorrection origin loop₂ = origin := by
  simp [twoLoopCorrection]

/-- Second loop divergent: correction origin. -/
theorem twoLoop_second_div [ValArith α] (loop₁ : Val α) :
    twoLoopCorrection loop₁ origin = origin := by
  simp [twoLoopCorrection]

-- ============================================================================
-- Part 7: Comparison — Standard vs Val
-- ============================================================================

-- STANDARD APPROACH:
--
--   theorem cross_section (M F : ℝ) (hF : F ≠ 0) :
--       σ = |M|²/F := ...
--
--   theorem perturbative (g : ℝ) (hg : g < 1) (M : ℝ) :
--       σ = g² * |M|² + O(g⁴) := ...
--   -- hg ensures the expansion converges
--
--   theorem two_loop (I₁ I₂ : ℝ) (h₁ : converges I₁) (h₂ : converges I₂) :
--       correction = I₁ + I₂ := ...

-- ============================================================================
-- Part 8: The Verdict
-- ============================================================================

-- DOES ORIGIN HANDLE QFT EXISTENCE BOUNDARIES?
--
-- Yes. The deepest existence boundaries in physics confirmed:
--   1. Bare vs renormalized: bare is origin, renormalized is contents
--   2. Landau pole: coupling is origin (theory breaks down)
--   3. UV/IR divergences: unregulated integral is origin
--   4. Flux boundary: cross section at zero flux is origin
--
-- Hypothesis count:
--
--   Theorem                         Standard              Val
--   ─────────────────────────────────────────────────────────────
--   obs_bare_coupling               h : renormalized       0
--   obs_bare_amplitude              h : renormalized       0
--   perturb_landau                  h : g < g_pole         0
--   loopObs_divergent               h : converges          0
--   loopObs_tree_origin             n/a                    0
--   xsec_flux_origin                h : F ≠ 0             0
--   xsec_bare                       h : renormalized       0
--   twoLoop_first_div               h₁ : converges        0
--   twoLoop_second_div              h₂ : converges        0
--   ─────────────────────────────────────────────────────────
--   Existence hypotheses dissolved:  8
--
-- FINAL RUNNING TOTAL — ALL SEVEN DOMAIN FILES:
--
--   PointCharge:        14
--   Vacuum:             17
--   Classical:           5
--   Thermodynamics:      9
--   Electromagnetism:    6
--   QuantumMechanics:   14
--   StatMech:            9
--   Relativity:          4
--   FieldTheory:         8
--   ─────────────────────
--   Total:              86 existence hypotheses dissolved
--
-- 86 existence hypotheses across 9 files, 7 domain files, covering
-- every major domain of physics from classical mechanics through QFT.
-- Same constructor. Same sort dispatch. Same proof pattern.
-- Origin captures the concept of existence boundary across all of physics.

end Val
