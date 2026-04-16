/-
Extracted from Order/Interval/Set/Defs.lean
Genuine: 9 | Conflates: 0 | Dissolved: 0 | Infrastructure: 16
-/
import Origin.Core
import Mathlib.Data.Set.Defs
import Mathlib.Order.Defs.PartialOrder

noncomputable section

/-!
# Intervals

In any preorder `α`, we define intervals
(which on each side can be either infinite, open, or closed)
using the following naming conventions:
- `i`: infinite
- `o`: open
- `c`: closed

Each interval has the name `I` + letter for left side + letter for right side.
For instance, `Ioc a b` denotes the interval `(a, b]`.

We also define a typeclass `Set.OrdConnected`
saying that a set includes `Set.Icc a b` whenever it contains both `a` and `b`.
-/

namespace Set

variable {α : Type*} [Preorder α] {a b x : α}

def Ioo (a b : α) := { x | a < x ∧ x < b }

def Ico (a b : α) := { x | a ≤ x ∧ x < b }

def Iio (b : α) := { x | x < b }

def Icc (a b : α) := { x | a ≤ x ∧ x ≤ b }

def Iic (b : α) := { x | x ≤ b }

def Ioc (a b : α) := { x | a < x ∧ x ≤ b }

def Ici (a : α) := { x | a ≤ x }

def Ioi (a : α) := { x | a < x }

class OrdConnected (s : Set α) : Prop where
  /-- `s : Set α` is `OrdConnected` if for all `x y ∈ s` it includes the interval `[[x, y]]`. -/
  out' ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s) : Icc x y ⊆ s

end Set
