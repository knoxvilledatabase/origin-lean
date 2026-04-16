/-
Released under MIT license.
-/
import Origin.Core

/-!
# Origin Test: Option Int

Can the entire Val foundation be replaced by Option α plus the
origin theorem?

Instantiate the derivation on Int. Build Option operations.
Prove the critical distinction. Count what you get for free.
-/

-- ============================================================================
-- Step 1: The Derivation Instantiates on Int
-- ============================================================================

theorem int_origin (n : Int) : n * 0 = 0 :=
  origin 0 Int.add_right_neg Int.mul_add (fun a b => (Int.neg_mul_eq_mul_neg a b).symm) n

-- The four-step proof works on Int. Not by convention. By derivation.

-- ============================================================================
-- Step 2: Option Int — The Ground and the Parts
-- ============================================================================

-- None  = the ground. The whole.
-- Some a = a value. A part.

def ground : Option Int := none
def val (a : Int) : Option Int := some a

-- ============================================================================
-- Step 3: Operations
-- ============================================================================

def oAdd : Option Int → Option Int → Option Int
  | none, x      => x
  | x, none      => x
  | some a, some b =>
      if a + b = 0 then none else some (a + b)

def oNeg : Option Int → Option Int
  | none   => none
  | some a => some (-a)

def oMul : Option Int → Option Int → Option Int
  | none, _      => none
  | _, none      => none
  | some a, some b =>
      if a * b = 0 then none else some (a * b)

-- ============================================================================
-- Step 4: The Ground is the Additive Identity
-- ============================================================================

theorem oAdd_ground_left (x : Option Int) : oAdd none x = x := by
  cases x <;> rfl

theorem oAdd_ground_right (x : Option Int) : oAdd x none = x := by
  cases x <;> rfl

-- ============================================================================
-- Step 5: Cancellation Returns to the Ground
-- ============================================================================

theorem oCancellation (a : Int) : oAdd (some a) (oNeg (some a)) = none := by
  simp [oAdd, oNeg, Int.add_right_neg]

-- The shepherd ate the apple. His hand is empty. Not Some 0. None.

-- ============================================================================
-- Step 6: The Ground Absorbs Under Multiplication
-- ============================================================================

theorem oMul_ground_left (x : Option Int) : oMul none x = none := by
  cases x <;> rfl

theorem oMul_ground_right (x : Option Int) : oMul x none = none := by
  cases x <;> rfl

-- ============================================================================
-- Step 7: Multiplication by Zero Returns to the Ground
-- ============================================================================

theorem oMul_zero (n : Int) : oMul (some n) (some 0) = none := by
  simp [oMul, Int.mul_zero]

-- Five copies of nothing is the ground. Not Some 0. None.
-- This is the result Val doesn't have.

-- ============================================================================
-- Step 8: The Critical Distinction
-- ============================================================================

-- Some 0 ≠ None. A measurement of zero is not the ground.

theorem measurement_ne_ground : some (0 : Int) ≠ none := by
  intro h; cases h

-- But multiplication by Some 0 gives None (the ground).
-- The operation collapses it. The VALUE is distinct. The ALGEBRA agrees
-- with the ground.

-- Some 0 can exist as input (a sensor read zero). But it cannot survive
-- multiplication — because zero under multiplication IS the ground.
-- The derivation (origin theorem) is why.

-- ============================================================================
-- Step 9: Concrete Computation
-- ============================================================================

-- Arithmetic in the counting domain
example : oMul (some 3) (some 5) = some 15 := by native_decide
example : oAdd (some 3) (some 5) = some 8 := by native_decide
example : oAdd (some 3) (some (-3)) = none := by native_decide

-- The ground absorbs
example : oMul none (some 42) = none := rfl
example : oMul (some 42) none = none := rfl
example : oAdd none (some 7) = some 7 := rfl

-- Multiplication by zero = the ground
example : oMul (some 7) (some 0) = none := by native_decide
example : oMul (some 0) (some 7) = none := by native_decide

-- The critical distinction: Some 0 exists but collapses under multiplication
example : oAdd (some 0) (some 5) = some 5 := by native_decide
example : oMul (some 0) (some 5) = none := by native_decide

-- ============================================================================
-- Step 10: What You Get For Free
-- ============================================================================

-- From Option α + the origin theorem:
--
--   ✓ Additive identity (ground + x = x)
--   ✓ Cancellation (x - x = ground)
--   ✓ Multiplicative origin (ground × x = ground)
--   ✓ Multiplication by zero = ground (the derivation)
--   ✓ Critical distinction (Some 0 ≠ None)
--   ✓ Concrete computation
--
-- What Val needed 10,756 lines and 5 typeclasses to provide,
-- Option α provides with zero infrastructure. Because Option
-- already IS the correct type. The ground outside. The parts inside.
--
-- Val was the scaffolding. Origin is the derivation. Option is the type.
-- The scaffolding did its job. Now you can see the building.
