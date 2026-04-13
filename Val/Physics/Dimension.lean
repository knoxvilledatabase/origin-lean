/-
Released under MIT license.
-/
import Val.Physics.Singularity

/-!
# Val Physics: Dimension — Type-Level Dimensional Analysis

Lean's type system, not Val's sort dispatch. A force and a velocity
both exist — they're counts of different kinds. That difference
belongs in the type system.

Five base dimensions (mass, length, time, temperature, current) as integer exponents.
Dimensional arithmetic is exponent addition. Lean prevents force + velocity
at compile time. No runtime checks. No origin corruption.

Val adds existence boundaries on top: Val (Quantity Force ℝ) can be origin
(force doesn't exist at this singularity) or contents (force has a value).
Two mechanisms. Each doing what it's best at.
-/

namespace Val

universe u

-- ============================================================================
-- Dimensions: Exponent Vectors
-- ============================================================================

/-- Physical dimension as exponents of base units: kg^mass · m^length · s^time · K^temp · A^current -/
structure Dim where
  mass : Int
  length : Int
  time : Int
  temp : Int
  current : Int
  deriving DecidableEq, Repr

namespace Dim

/-- Multiply dimensions: add exponents. mass × acceleration = force. -/
def mul (a b : Dim) : Dim :=
  ⟨a.mass + b.mass, a.length + b.length, a.time + b.time, a.temp + b.temp, a.current + b.current⟩

/-- Invert dimension: negate exponents. -/
def inv (a : Dim) : Dim :=
  ⟨-a.mass, -a.length, -a.time, -a.temp, -a.current⟩

/-- Divide dimensions: multiply by inverse. -/
def div (a b : Dim) : Dim := a.mul b.inv

-- ============================================================================
-- Common Dimensions
-- ============================================================================

-- Mechanical
def scalar : Dim := ⟨0, 0, 0, 0, 0⟩
def M : Dim := ⟨1, 0, 0, 0, 0⟩              -- mass (kg)
def L : Dim := ⟨0, 1, 0, 0, 0⟩              -- length (m)
def T : Dim := ⟨0, 0, 1, 0, 0⟩              -- time (s)
def velocity : Dim := ⟨0, 1, -1, 0, 0⟩       -- m/s
def acceleration : Dim := ⟨0, 1, -2, 0, 0⟩   -- m/s²
def force : Dim := ⟨1, 1, -2, 0, 0⟩          -- kg·m/s² (Newton)
def energy : Dim := ⟨1, 2, -2, 0, 0⟩         -- kg·m²/s² (Joule)
def momentum : Dim := ⟨1, 1, -1, 0, 0⟩       -- kg·m/s
def power : Dim := ⟨1, 2, -3, 0, 0⟩          -- kg·m²/s³ (Watt)
def area : Dim := ⟨0, 2, 0, 0, 0⟩            -- m²
def potentialCoeff : Dim := ⟨1, 3, -2, 0, 0⟩ -- energy × length (for V = coeff/r)

-- Thermodynamic
def temperature : Dim := ⟨0, 0, 0, 1, 0⟩      -- Kelvin
def entropy : Dim := ⟨1, 2, -2, -1, 0⟩        -- J/K (energy/temperature)
def pressure : Dim := ⟨1, -1, -2, 0, 0⟩       -- Pa (force/area)
def volume : Dim := ⟨0, 3, 0, 0, 0⟩           -- m³
def specificHeat : Dim := ⟨0, 2, -2, -1, 0⟩   -- J/(kg·K)

-- Electromagnetic
def current_ : Dim := ⟨0, 0, 0, 0, 1⟩          -- Ampere
def charge : Dim := ⟨0, 0, 1, 0, 1⟩            -- Coulomb (A·s)
def electricField : Dim := ⟨1, 1, -3, 0, -1⟩   -- V/m (force/charge)
def magneticField : Dim := ⟨1, 0, -2, 0, -1⟩   -- Tesla (force/(charge·velocity))
def energyDensity : Dim := ⟨1, -1, -2, 0, 0⟩   -- J/m³ (energy/volume)
def permittivity : Dim := ⟨-1, -3, 4, 0, 2⟩    -- F/m (ε₀)
def invPermeability : Dim := ⟨-1, -1, 2, 0, 2⟩ -- 1/(H/m) (1/μ₀)

-- ============================================================================
-- Dimensional Algebra: Verified by rfl
-- ============================================================================

-- Mechanical
example : M.mul acceleration = force := rfl
example : force.mul L = energy := rfl
example : M.mul velocity = momentum := rfl
example : energy.div T = power := rfl
example : velocity.mul T = L := rfl
example : M.mul (velocity.mul velocity) = energy := rfl
example : potentialCoeff.div L = energy := rfl

-- Thermodynamic
example : energy.div temperature = entropy := rfl
example : entropy.mul temperature = energy := rfl
example : force.div area = pressure := rfl
example : pressure.mul volume = energy := rfl
example : energy.div (M.mul temperature) = specificHeat := rfl

-- Electromagnetic
example : force.div charge = electricField := rfl
example : charge.mul electricField = force := rfl
example : charge.mul (velocity.mul magneticField) = force := rfl
example : permittivity.mul (electricField.mul electricField) = energyDensity := rfl
example : invPermeability.mul (magneticField.mul magneticField) = energyDensity := rfl
example : potentialCoeff.div area = force := rfl

end Dim

-- ============================================================================
-- Quantity: A Value Tagged with Its Dimension
-- ============================================================================

variable {α : Type u}

/-- A physical quantity: a value of type α with dimension d. -/
structure Quantity (d : Dim) (α : Type u) where
  val : α

-- ============================================================================
-- ValArith Instance: Same-Dimension Operations
-- ============================================================================

-- Addition requires matching dimensions. Lean's type system enforces this:
-- add : Val (Quantity d α) → Val (Quantity d α) → Val (Quantity d α)
-- Force + velocity doesn't compile. Force + force does.

instance (d : Dim) [ValArith α] : ValArith (Quantity d α) where
  mulF q₁ q₂ := ⟨ValArith.mulF q₁.val q₂.val⟩
  addF q₁ q₂ := ⟨ValArith.addF q₁.val q₂.val⟩
  negF q := ⟨ValArith.negF q.val⟩
  invF q := ⟨ValArith.invF q.val⟩

-- ============================================================================
-- Cross-Dimension Operations (via liftBin₂)
-- ============================================================================

/-- Multiply quantities of different dimensions. mass × acceleration = force. -/
def mulQ [ValArith α] {d₁ d₂ : Dim} :
    Val (Quantity d₁ α) → Val (Quantity d₂ α) → Val (Quantity (d₁.mul d₂) α) :=
  liftBin₂ (fun q₁ q₂ => ⟨ValArith.mulF q₁.val q₂.val⟩)

/-- Divide quantities. energy / time = power. -/
def divQ [ValArith α] {d₁ d₂ : Dim} :
    Val (Quantity d₁ α) → Val (Quantity d₂ α) → Val (Quantity (d₁.div d₂) α) :=
  liftBin₂ (fun q₁ q₂ => ⟨ValArith.mulF q₁.val (ValArith.invF q₂.val)⟩)

-- ============================================================================
-- Simp Set
-- ============================================================================

@[simp] theorem mulQ_origin_left [ValArith α] {d₁ d₂ : Dim}
    (b : Val (Quantity d₂ α)) :
    mulQ (origin : Val (Quantity d₁ α)) b = origin := by
  cases b <;> rfl

@[simp] theorem mulQ_origin_right [ValArith α] {d₁ d₂ : Dim}
    (a : Val (Quantity d₁ α)) :
    mulQ a (origin : Val (Quantity d₂ α)) = origin := by
  cases a <;> rfl

@[simp] theorem mulQ_contents [ValArith α] {d₁ d₂ : Dim}
    (a : Quantity d₁ α) (b : Quantity d₂ α) :
    mulQ (contents a) (contents b) =
    contents (⟨ValArith.mulF a.val b.val⟩ : Quantity (d₁.mul d₂) α) := rfl

@[simp] theorem divQ_origin_left [ValArith α] {d₁ d₂ : Dim}
    (b : Val (Quantity d₂ α)) :
    divQ (origin : Val (Quantity d₁ α)) b = origin := by
  cases b <;> rfl

@[simp] theorem divQ_origin_right [ValArith α] {d₁ d₂ : Dim}
    (a : Val (Quantity d₁ α)) :
    divQ a (origin : Val (Quantity d₂ α)) = origin := by
  cases a <;> rfl

@[simp] theorem divQ_contents [ValArith α] {d₁ d₂ : Dim}
    (a : Quantity d₁ α) (b : Quantity d₂ α) :
    divQ (contents a) (contents b) =
    contents (⟨ValArith.mulF a.val (ValArith.invF b.val)⟩ : Quantity (d₁.div d₂) α) := rfl

-- ============================================================================
-- Helpers
-- ============================================================================

/-- Wrap a raw value as a dimensioned quantity. -/
def mkQ (d : Dim) {α : Type u} (v : α) : Quantity d α := ⟨v⟩

/-- Lift a raw Val into a dimensioned Val. -/
def liftQ (d : Dim) {α : Type u} : Val α → Val (Quantity d α) :=
  valMap (mkQ d)

@[simp] theorem liftQ_origin (d : Dim) :
    liftQ d (origin : Val α) = origin := rfl

@[simp] theorem liftQ_contents (d : Dim) (v : α) :
    liftQ d (contents v) = contents (mkQ d v) := rfl

end Val
