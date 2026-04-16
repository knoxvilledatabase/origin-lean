/-
Released under MIT license.
-/
import Origin.Core

/-!
# Origin Physics: Option α Is Sufficient

The Val physics layer used 3,000 lines across 11 files to dissolve
86 existence hypotheses. This file shows the same dissolution using
Option α — the standard library type. No custom infrastructure.

None  = the ground. The field doesn't apply here.
Some a = a value. The field exists. The physics computes.
-/

universe u

-- ============================================================================
-- Dimensional Analysis (unchanged)
-- ============================================================================

structure Dim where
  mass : Int
  length : Int
  time : Int
  temp : Int
  current : Int
deriving DecidableEq, Repr

namespace Dim
def mul (a b : Dim) : Dim :=
  ⟨a.mass + b.mass, a.length + b.length, a.time + b.time, a.temp + b.temp, a.current + b.current⟩
def inv (a : Dim) : Dim :=
  ⟨-a.mass, -a.length, -a.time, -a.temp, -a.current⟩
def div (a b : Dim) : Dim := a.mul b.inv

def M : Dim := ⟨1, 0, 0, 0, 0⟩
def L : Dim := ⟨0, 1, 0, 0, 0⟩
def velocity : Dim := ⟨0, 1, -1, 0, 0⟩
def acceleration : Dim := ⟨0, 1, -2, 0, 0⟩
def force : Dim := ⟨1, 1, -2, 0, 0⟩
def energy : Dim := ⟨1, 2, -2, 0, 0⟩
def temperature : Dim := ⟨0, 0, 0, 1, 0⟩
def entropy : Dim := ⟨1, 2, -2, -1, 0⟩
def potentialCoeff : Dim := ⟨1, 3, -2, 0, 0⟩
def charge : Dim := ⟨0, 0, 1, 0, 1⟩
def electricField : Dim := ⟨1, 1, -3, 0, -1⟩
def area : Dim := ⟨0, 2, 0, 0, 0⟩

example : M.mul acceleration = force := rfl
example : M.mul (velocity.mul velocity) = energy := rfl
example : energy.div temperature = entropy := rfl
example : potentialCoeff.div area = force := rfl
end Dim

structure Quantity (d : Dim) (α : Type u) where
  val : α

-- ============================================================================
-- Cross-Dimensional Operations (using liftBin₂ from Core)
-- ============================================================================

variable {α : Type u}

def mulQ [Mul α] {d₁ d₂ : Dim} :
    Option (Quantity d₁ α) → Option (Quantity d₂ α) → Option (Quantity (d₁.mul d₂) α) :=
  liftBin₂ (fun q₁ q₂ => ⟨q₁.val * q₂.val⟩)

def divQ [Mul α] {d₁ d₂ : Dim} (invF : α → α) :
    Option (Quantity d₁ α) → Option (Quantity d₂ α) → Option (Quantity (d₁.div d₂) α) :=
  liftBin₂ (fun q₁ q₂ => ⟨q₁.val * invF q₂.val⟩)

@[simp] theorem mulQ_none_left [Mul α] {d₁ d₂ : Dim}
    (b : Option (Quantity d₂ α)) :
    mulQ (none : Option (Quantity d₁ α)) b = none := by cases b <;> rfl

@[simp] theorem mulQ_none_right [Mul α] {d₁ d₂ : Dim}
    (a : Option (Quantity d₁ α)) :
    mulQ a (none : Option (Quantity d₂ α)) = none := by cases a <;> rfl

@[simp] theorem divQ_none_left [Mul α] {d₁ d₂ : Dim} (invF : α → α)
    (b : Option (Quantity d₂ α)) :
    divQ invF (none : Option (Quantity d₁ α)) b = none := by cases b <;> rfl

@[simp] theorem divQ_none_right [Mul α] {d₁ d₂ : Dim} (invF : α → α)
    (a : Option (Quantity d₁ α)) :
    divQ invF a (none : Option (Quantity d₂ α)) = none := by cases a <;> rfl

-- ============================================================================
-- Classical Mechanics: F = ma
-- ============================================================================

def newtonForce [Mul α]
    (mass : Option (Quantity Dim.M α))
    (accel : Option (Quantity Dim.acceleration α)) :
    Option (Quantity Dim.force α) :=
  mulQ mass accel

/-- Mass not in counting domain: neither is force. -/
theorem newton_mass_none [Mul α]
    (accel : Option (Quantity Dim.acceleration α)) :
    newtonForce (none : Option (Quantity Dim.M α)) accel = none := by
  simp [newtonForce]

/-- Acceleration not in counting domain: neither is force. -/
theorem newton_accel_none [Mul α]
    (mass : Option (Quantity Dim.M α)) :
    newtonForce mass (none : Option (Quantity Dim.acceleration α)) = none := by
  simp [newtonForce]

-- ============================================================================
-- Point Charge: F = coeff/r²
-- ============================================================================

def coulombForce [Mul α]
    (invF : α → α)
    (coeff : Option (Quantity Dim.potentialCoeff α))
    (r : Option (Quantity Dim.L α)) :
    Option (Quantity Dim.force α) :=
  divQ invF coeff (mulQ r r)

/-- Singularity: field concept doesn't apply. -/
theorem coulomb_r_none [Mul α] (invF : α → α)
    (coeff : Option (Quantity Dim.potentialCoeff α)) :
    coulombForce invF coeff (none : Option (Quantity Dim.L α)) = none := by
  simp [coulombForce]

-- ============================================================================
-- Thermodynamics: dS = dQ/T
-- ============================================================================

def entropyChange [Mul α]
    (invF : α → α)
    (dQ : Option (Quantity Dim.energy α))
    (temp : Option (Quantity Dim.temperature α)) :
    Option (Quantity Dim.entropy α) :=
  divQ invF dQ temp

/-- Absolute zero: entropy concept doesn't apply. -/
theorem entropy_temp_none [Mul α] (invF : α → α)
    (dQ : Option (Quantity Dim.energy α)) :
    entropyChange invF dQ (none : Option (Quantity Dim.temperature α)) = none := by
  simp [entropyChange]

-- ============================================================================
-- Electromagnetism: F = qE
-- ============================================================================

def lorentzElectric [Mul α]
    (q : Option (Quantity Dim.charge α))
    (e : Option (Quantity Dim.electricField α)) :
    Option (Quantity Dim.force α) :=
  mulQ q e

/-- No charge: force concept doesn't apply. -/
theorem lorentz_q_none [Mul α]
    (e : Option (Quantity Dim.electricField α)) :
    lorentzElectric (none : Option (Quantity Dim.charge α)) e = none := by
  simp [lorentzElectric]

-- ============================================================================
-- Quantum Mechanics: ⟨ψ|Â|ψ⟩
-- ============================================================================

def expectation [Mul α] (coupling : α) (state : Option α) : Option α :=
  state.map (coupling * ·)

/-- Vacuum: counting doesn't apply. -/
theorem expect_none [Mul α] (c : α) :
    expectation c (none : Option α) = none := rfl

/-- Occupied: computes. -/
theorem expect_some [Mul α] (c a : α) :
    expectation c (some a) = some (c * a) := rfl

-- ============================================================================
-- Two Sources: Independent Boundaries
-- ============================================================================

def twoSourceForce [Mul α] [Add α]
    (invF : α → α)
    (c₁ c₂ : Option (Quantity Dim.potentialCoeff α))
    (r₁ r₂ : Option (Quantity Dim.L α)) :
    Option (Quantity Dim.force α) :=
  liftBin₂ (fun a b => ⟨a.val + b.val⟩) (coulombForce invF c₁ r₁) (coulombForce invF c₂ r₂)

/-- First source at singularity: total force not in counting domain. -/
theorem twoSource_r1_none [Mul α] [Add α] (invF : α → α)
    (c₁ c₂ : Option (Quantity Dim.potentialCoeff α))
    (r₂ : Option (Quantity Dim.L α)) :
    twoSourceForce invF c₁ c₂ none r₂ = none := by
  simp [twoSourceForce, coulombForce]

/-- Second source at singularity: total force not in counting domain. -/
theorem twoSource_r2_none [Mul α] [Add α] (invF : α → α)
    (c₁ c₂ : Option (Quantity Dim.potentialCoeff α))
    (r₁ : Option (Quantity Dim.L α)) :
    twoSourceForce invF c₁ c₂ r₁ none = none := by
  simp [twoSourceForce, coulombForce]

-- ============================================================================
-- The Verdict
-- ============================================================================

-- Every theorem: zero existence hypotheses. Same as Val.
-- Same dissolution. Same proof pattern. Same result.
--
-- What's gone:
--   Foundation.lean, Arith.lean, Ring.lean, Field.lean,
--   OrderedField.lean, Module.lean. The five-level class hierarchy.
--   The custom simp set. All of it.
--
-- What remains:
--   Option. liftBin₂ (4 lines). Dim. Quantity. The physics.
--
-- Domains demonstrated:
--   Classical mechanics:  F = ma, none absorbs           ✓
--   Point charge:         Coulomb, singularity = none    ✓
--   Thermodynamics:       entropy, absolute zero = none  ✓
--   Electromagnetism:     Lorentz force, q = none        ✓
--   Quantum mechanics:    expectation, vacuum = none     ✓
--   Two-source:           independent boundaries         ✓
--
-- Val was the scaffolding. Option is the building.
