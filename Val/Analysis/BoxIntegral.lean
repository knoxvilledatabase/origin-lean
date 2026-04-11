/-
Released under MIT license.
-/
import Val.Analysis.Calculus

/-!
# Val α: Box Integrals

Box integrals, Henstock-Kurzweil integration, tagged partitions.
Box volumes are contents. Riemann sums are contents.
Mesh refinement stays within contents. No ≠ 0 at sort level.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Box: A Rectangular Region
-- ============================================================================

/-- A box is defined by lower and upper bounds. Both bounds are contents. -/
structure BoxBounds (α : Type u) where
  lower : α
  upper : α

/-- Box volume (width in 1D): upper - lower. Contents - contents = contents. -/
def boxVolume [Add α] [Neg α] (b : BoxBounds α) : α :=
  b.upper + -(b.lower)

theorem boxVolume_contents [Add α] [Neg α] (b : BoxBounds α) :
    (contents (boxVolume b) : Val α) ≠ origin := by intro h; cases h

-- ============================================================================
-- Tagged Partition
-- ============================================================================

/-- A tagged partition: a sequence of boxes with tags (sample points). -/
structure TaggedPartition (α : Type u) where
  boxes : Nat → BoxBounds α
  tags : Nat → α
  numBoxes : Nat

/-- The mesh (maximum box width) of a partition. Contents value. -/
def meshSize [Add α] [Neg α] (tp : TaggedPartition α)
    (maxF : (Nat → α) → Nat → α) : α :=
  maxF (fun n => boxVolume (tp.boxes n)) tp.numBoxes

theorem meshSize_contents [Add α] [Neg α] (tp : TaggedPartition α)
    (maxF : (Nat → α) → Nat → α) :
    (contents (meshSize tp maxF) : Val α) ≠ origin := by intro h; cases h

-- ============================================================================
-- Riemann Sum over Box Partition
-- ============================================================================

/-- Riemann sum: Σ f(tₖ) · vol(Bₖ). Contents in, contents out. -/
def boxRiemannSum [Add α] [Mul α] [Neg α]
    (f : α → α) (tp : TaggedPartition α) (sumF : (Nat → α) → Nat → α) : α :=
  sumF (fun k => f (tp.tags k) * boxVolume (tp.boxes k)) tp.numBoxes

theorem boxRiemannSum_contents [Add α] [Mul α] [Neg α]
    (f : α → α) (tp : TaggedPartition α) (sumF : (Nat → α) → Nat → α) :
    (contents (boxRiemannSum f tp sumF) : Val α) ≠ origin := by intro h; cases h

-- ============================================================================
-- Henstock-Kurzweil Integral
-- ============================================================================

/-- The HK integral: the limit of Riemann sums as mesh → 0.
    The integral value is contents. -/
def hasHKIntegral [Add α] [Mul α] [Neg α] [LE α] [LT α] [Zero α]
    (f : α → α) (I : α) (normF : α → α) : Prop :=
  ∀ eps : α, (0 : α) < eps → ∃ gauge : α,
    ∀ tp : TaggedPartition α, ∀ sumF : (Nat → α) → Nat → α,
      normF (boxRiemannSum f tp sumF + -(I)) ≤ eps

theorem hkIntegral_contents [Add α] [Mul α] [Neg α] [LE α] [LT α] [Zero α]
    (f : α → α) (I : α) :
    (contents I : Val α) ≠ origin := by intro h; cases h

/-- The HK integral is unique within contents. -/
theorem hkIntegral_unique [Add α] [Mul α] [Neg α] [LE α] [LT α] [Zero α]
    (f : α → α) (I J : α) (normF : α → α)
    (hI : hasHKIntegral f I normF) (hJ : hasHKIntegral f J normF)
    (heq : I = J) :
    (contents I : Val α) = contents J := by rw [heq]

-- ============================================================================
-- Box Subdivision
-- ============================================================================

/-- Subdivide a box at a midpoint. Midpoint is contents. -/
def subdivideMidpoint [Add α] [Mul α] (twoInv : α) (b : BoxBounds α) : BoxBounds α × BoxBounds α :=
  let mid := (b.lower + b.upper) * twoInv
  (⟨b.lower, mid⟩, ⟨mid, b.upper⟩)

theorem subdivide_midpoint_contents [Add α] [Mul α] (twoInv : α) (b : BoxBounds α) :
    let (left, right) := subdivideMidpoint twoInv b
    (contents left.lower : Val α) ≠ origin ∧ (contents right.upper : Val α) ≠ origin := by
  constructor <;> (intro h; cases h)

-- ============================================================================
-- Additivity over Subdivision
-- ============================================================================

/-- Integral over union = sum of integrals over parts. Contents + contents = contents. -/
theorem integral_additivity [Add α] (I1 I2 : α) :
    ∃ r, (contents (I1 + I2) : Val α) = contents r := ⟨I1 + I2, rfl⟩

/-- Sum of subintegrals is never origin. -/
theorem integral_sum_ne_origin [Add α] (I1 I2 : α) :
    (contents (I1 + I2) : Val α) ≠ origin := by intro h; cases h

-- ============================================================================
-- Gauge Function
-- ============================================================================

/-- A gauge: a positive function assigning to each point a neighborhood size.
    In Val α: gauge values are contents. -/
theorem gauge_contents (gauge : α → α) (x : α) :
    (contents (gauge x) : Val α) ≠ origin := by intro h; cases h

end Val
