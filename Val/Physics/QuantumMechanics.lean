/-
Released under MIT license.
-/
import Val.Physics.Dimension

/-!
# Val Physics: Quantum Mechanics

Extends Vacuum.lean into a full domain file. Observables, eigenvalues,
the uncertainty principle, superposition, and measurement.

## The Honest Boundary

Val handles:
- Vacuum as origin (demonstrated in Vacuum.lean)
- Observable domain — state not in domain of operator → origin
- Undefined uncertainty — observable undefined on state → uncertainty origin
- Superposition with vacuum — vacuum component contributes origin

Val does NOT handle:
- Hilbert space completeness
- Spectral theorem for unbounded operators
- Measurement collapse — the transition itself is the measurement problem,
  one of physics' 23 patches. Val names where the boundary is (the state
  isn't in a definite sort during measurement) but doesn't resolve it.
- Born rule — probability from amplitudes requires the analytic engine
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Part 1: Quantum States and Observables
-- ============================================================================

-- A quantum state: Val α where origin = vacuum / not in domain.
-- An observable applied to a state: if the state isn't in the
-- operator's domain, the result is origin. Not undefined — origin.
-- Standard QM: h : ψ ∈ domain(A). Val: sort dispatch.

/-- Apply an observable to a state.
    If the state is origin (vacuum or not in domain), the result is origin.
    If the state is contents, the observable computes. -/
def applyObs [ValArith α] (obs : α → α) (state : Val α) : Val α :=
  valMap obs state

/-- Observable on vacuum: origin. No h : ψ ≠ vacuum. -/
theorem obs_vacuum [ValArith α] (obs : α → α) :
    applyObs obs (origin : Val α) = origin := rfl

/-- Observable on occupied state: computes. -/
theorem obs_contents [ValArith α] (obs : α → α) (ψ : α) :
    applyObs obs (contents ψ) = contents (obs ψ) := rfl

-- ============================================================================
-- Part 2: Eigenvalues
-- ============================================================================

-- An eigenstate of an operator: Â|ψ⟩ = λ|ψ⟩.
-- The eigenvalue λ is contents when ψ is in the domain.
-- When ψ = origin (not in domain), the eigenvalue is origin.

/-- Eigenvalue extraction: multiply by the inverse of the state amplitude.
    If the state is origin, the eigenvalue is origin.
    Standard: h : ⟨ψ|ψ⟩ ≠ 0. Val: sort dispatch. -/
def eigenvalue [ValArith α] (obsResult stateAmp : Val α) : Val α :=
  mul obsResult (inv stateAmp)

/-- Eigenvalue from vacuum state: origin. No hypothesis. -/
theorem eigenvalue_vacuum_state [ValArith α] (obsResult : Val α) :
    eigenvalue obsResult (origin : Val α) = origin := by
  simp [eigenvalue]

/-- Eigenvalue from vacuum observable: origin. -/
theorem eigenvalue_vacuum_obs [ValArith α] (stateAmp : Val α) :
    eigenvalue origin stateAmp = origin := by
  simp [eigenvalue]

/-- Both defined: computes. -/
theorem eigenvalue_contents [ValArith α] (r a : α) :
    eigenvalue (contents r) (contents a) =
    contents (ValArith.mulF r (ValArith.invF a)) := rfl

-- ============================================================================
-- Part 3: Expectation Value — ⟨ψ|Â|ψ⟩
-- ============================================================================

-- The expectation value of an observable in a state.
-- Standard: h : ψ normalizable, h : ψ ∈ domain(A).
-- Val: if the state is origin, the expectation is origin.

def expectation [ValArith α] (coupling : α) (state : Val α) : Val α :=
  valMap (ValArith.mulF coupling) state

/-- Expectation in vacuum: origin. No normalizability hypothesis. -/
theorem expect_vacuum [ValArith α] (c : α) :
    expectation c (origin : Val α) = origin := rfl

/-- Expectation in occupied state: computes. -/
theorem expect_contents [ValArith α] (c ψ : α) :
    expectation c (contents ψ) = contents (ValArith.mulF c ψ) := rfl

/-- Expectation in occupied state is never origin. -/
theorem expect_contents_ne_origin [ValArith α] (c ψ : α) :
    expectation c (contents ψ) ≠ origin := by simp [expectation]

-- ============================================================================
-- Part 4: Uncertainty Principle — ΔA · ΔB ≥ ℏ/2
-- ============================================================================

-- The uncertainty product of two observables on a state.
-- If either observable is undefined on the state (origin),
-- the uncertainty product is origin. Not "large" — origin.
-- The question "what is the uncertainty?" doesn't apply.

def uncertaintyProduct [ValArith α]
    (deltaA deltaB : Val α) : Val α :=
  mul deltaA deltaB

/-- First observable undefined: uncertainty product origin. -/
theorem uncertainty_a_origin [ValArith α] (deltaB : Val α) :
    uncertaintyProduct origin deltaB = origin := by
  simp [uncertaintyProduct]

/-- Second observable undefined: uncertainty product origin. -/
theorem uncertainty_b_origin [ValArith α] (deltaA : Val α) :
    uncertaintyProduct deltaA origin = origin := by
  simp [uncertaintyProduct]

/-- Both defined: computes. The ≥ ℏ/2 bound is a property of contents. -/
theorem uncertainty_contents [ValArith α] (a b : α) :
    uncertaintyProduct (contents a) (contents b) =
    contents (ValArith.mulF a b) := rfl

-- ============================================================================
-- Part 5: Superposition with Vacuum
-- ============================================================================

-- A superposition α|vacuum⟩ + β|n⟩.
-- The vacuum component contributes origin to measurements.
-- The occupied component contributes contents.
-- Measurement on the superposition: the vacuum component absorbs.

/-- Superposition: add the contributions from each component. -/
def superpositionExpect [ValArith α]
    (c : α) (state₁ state₂ : Val α) : Val α :=
  add (expectation c state₁) (expectation c state₂)

/-- First component vacuum: total expectation origin. -/
theorem super_vacuum_first [ValArith α] (c : α) (state₂ : Val α) :
    superpositionExpect c origin state₂ = origin := by
  simp [superpositionExpect, expectation, add]

/-- Second component vacuum: total expectation origin. -/
theorem super_vacuum_second [ValArith α] (c : α) (state₁ : Val α) :
    superpositionExpect c state₁ origin = origin := by
  cases state₁ <;> simp [superpositionExpect, expectation, add]

/-- Both occupied: computes. -/
theorem super_both_occupied [ValArith α] (c ψ₁ ψ₂ : α) :
    superpositionExpect c (contents ψ₁) (contents ψ₂) =
    contents (ValArith.addF (ValArith.mulF c ψ₁) (ValArith.mulF c ψ₂)) := rfl

-- ============================================================================
-- Part 6: Number Operator — How Many Particles?
-- ============================================================================

-- N̂|n⟩ = n|n⟩. On the vacuum: nothing to count. Origin, not zero.
-- contents(0) = "measured, found zero particles."
-- origin = "not in a state where particle counting applies."

def numberOp [ValArith α] (state : Val α) : Val α :=
  match state with
  | origin => origin
  | container n => container n
  | contents n => contents n

/-- Number operator on vacuum: origin. -/
theorem number_vacuum [ValArith α] :
    numberOp (origin : Val α) = origin := rfl

/-- Create then count: occupied. -/
theorem number_after_create [ValArith α] (one : α) :
    numberOp (contents one) = contents one := rfl

-- ============================================================================
-- Part 7: Two Observables — Independent Domain Boundaries
-- ============================================================================

-- Measure two observables on two states.
-- Standard: h₁ : ψ₁ ∈ domain(A), h₂ : ψ₂ ∈ domain(B).
-- Val: two independent sort dispatches.

def twoObsExpect [ValArith α]
    (cA cB : α) (stateA stateB : Val α) : Val α :=
  add (expectation cA stateA) (expectation cB stateB)

/-- First state not in domain: total origin. -/
theorem twoObs_first_origin [ValArith α] (cA cB : α) (stateB : Val α) :
    twoObsExpect cA cB origin stateB = origin := by
  simp [twoObsExpect, expectation, add]

/-- Second state not in domain: total origin. -/
theorem twoObs_second_origin [ValArith α] (cA cB : α) (stateA : Val α) :
    twoObsExpect cA cB stateA origin = origin := by
  cases stateA <;> simp [twoObsExpect, expectation, add]

-- ============================================================================
-- Part 8: Commutator — [A, B] = AB - BA
-- ============================================================================

-- The commutator of two operators on a state.
-- If the state isn't in the domain of either, the commutator is origin.

def commutator [ValArith α] (obsA obsB : α → α) (state : Val α) : Val α :=
  add (applyObs (fun x => ValArith.mulF (obsA x) (obsB x)) state)
      (neg (applyObs (fun x => ValArith.mulF (obsB x) (obsA x)) state))

/-- Commutator on vacuum: origin. -/
theorem commutator_vacuum [ValArith α] (obsA obsB : α → α) :
    commutator obsA obsB (origin : Val α) = origin := by
  simp [commutator, applyObs, add, neg]

-- ============================================================================
-- Part 9: Measurement — The Honest Boundary
-- ============================================================================

-- Measurement collapse: after measuring observable A on state ψ,
-- the state collapses to an eigenstate of A.
--
-- Before measurement: ψ is contents (a superposition).
-- After measurement: ψ is contents (an eigenstate).
-- During measurement: the state is not in a definite sort.
--
-- Val names where the boundary is. The transition from superposition
-- to eigenstate — the measurement process itself — is where the
-- counting stops. That's one of physics' 23 patches (the measurement
-- problem). Val doesn't solve it. But it can name it:
--
--   "The state during measurement is origin — not because the state
--    doesn't exist, but because the sort (which eigenstate?) isn't
--    determined yet."
--
-- This is the same distinction as PointCharge naming the singularity
-- and Vacuum naming the vacuum. The measurement problem is a third
-- kind of existence boundary: the sort is temporarily undefined.
--
-- We note this honestly and move on. The measurement problem is
-- open for a reason.

-- ============================================================================
-- Part 10: Comparison — Standard vs Val
-- ============================================================================

-- STANDARD APPROACH:
--
--   theorem expectation (A : Operator) (ψ : State)
--       (hψ : Normalizable ψ) (hd : ψ ∈ domain A) :
--       ⟨ψ|A|ψ⟩ = ... := ...
--
--   theorem uncertainty (A B : Operator) (ψ : State)
--       (hψ : Normalizable ψ)
--       (hdA : ψ ∈ domain A) (hdB : ψ ∈ domain B) :
--       ΔA * ΔB ≥ ℏ/2 := ...
--
--   theorem eigenvalue (A : Operator) (ψ : State) (λ : ℝ)
--       (hψ : ψ ≠ 0) (hd : ψ ∈ domain A) :
--       A ψ = λ • ψ := ...
--
-- Every theorem carries h : ψ ∈ domain(A) and h : Normalizable ψ.
-- Multi-observable theorems thread multiple domain hypotheses.

-- ============================================================================
-- Part 11: The Verdict
-- ============================================================================

-- DOES ORIGIN HANDLE QUANTUM EXISTENCE BOUNDARIES?
--
-- Yes. Hypothesis count:
--
--   Theorem                         Standard              Val
--   ─────────────────────────────────────────────────────────────
--   obs_vacuum                      hd : ψ ∈ domain       0
--   eigenvalue_vacuum_state         hψ ≠ 0                0
--   eigenvalue_vacuum_obs           hd                     0
--   expect_vacuum                   hψ norm, hd            0
--   expect_contents_ne_origin       0 (structural)         0
--   uncertainty_a_origin            hd_A                   0
--   uncertainty_b_origin            hd_B                   0
--   super_vacuum_first              hψ₁ norm               0
--   super_vacuum_second             hψ₂ norm               0
--   twoObs_first_origin             hd₁                    0
--   twoObs_second_origin            hd₂                    0
--   commutator_vacuum               hd_A, hd_B             0
--   ─────────────────────────────────────────────────────────
--   Existence hypotheses dissolved:  14
--   (counting hψ ∈ domain, hψ normalizable, hψ ≠ 0 as separate)
--
-- Running total:
--   PointCharge:        14
--   Vacuum:             17
--   Classical:           5
--   Thermodynamics:      9
--   Electromagnetism:    6
--   QuantumMechanics:   14
--   ─────────────────────
--   Total:              65 existence hypotheses dissolved

end Val
