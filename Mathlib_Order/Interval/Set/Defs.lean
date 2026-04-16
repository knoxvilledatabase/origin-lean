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

@[simp] theorem mem_Ioo : x ∈ Ioo a b ↔ a < x ∧ x < b := Iff.rfl

def Ico (a b : α) := { x | a ≤ x ∧ x < b }

@[simp] theorem mem_Ico : x ∈ Ico a b ↔ a ≤ x ∧ x < b := Iff.rfl

def Iio (b : α) := { x | x < b }

@[simp] theorem mem_Iio : x ∈ Iio b ↔ x < b := Iff.rfl

def Icc (a b : α) := { x | a ≤ x ∧ x ≤ b }

@[simp] theorem mem_Icc : x ∈ Icc a b ↔ a ≤ x ∧ x ≤ b := Iff.rfl

def Iic (b : α) := { x | x ≤ b }

@[simp] theorem mem_Iic : x ∈ Iic b ↔ x ≤ b := Iff.rfl

def Ioc (a b : α) := { x | a < x ∧ x ≤ b }

@[simp] theorem mem_Ioc : x ∈ Ioc a b ↔ a < x ∧ x ≤ b := Iff.rfl

def Ici (a : α) := { x | a ≤ x }

@[simp] theorem mem_Ici : x ∈ Ici a ↔ a ≤ x := Iff.rfl

def Ioi (a : α) := { x | a < x }

@[simp] theorem mem_Ioi : x ∈ Ioi a ↔ a < x := Iff.rfl

class OrdConnected (s : Set α) : Prop where
  /-- `s : Set α` is `OrdConnected` if for all `x y ∈ s` it includes the interval `[[x, y]]`. -/
  out' ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s) : Icc x y ⊆ s

end Set
