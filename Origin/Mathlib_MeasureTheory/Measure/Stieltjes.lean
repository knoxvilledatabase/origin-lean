/-
Extracted from MeasureTheory/Measure/Stieltjes.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Stieltjes measures on the real line

Consider a function `f : ℝ → ℝ` which is monotone and right-continuous. Then one can define a
corresponding measure, giving mass `f b - f a` to the interval `(a, b]`. We implement more
generally this notion for `f : R → ℝ` where `R` is a conditionally complete dense linear order.

## Main definitions

* `StieltjesFunction R` is a structure containing a function from `R → ℝ`, together with the
  assertions that it is monotone and right-continuous. To `f : StieltjesFunction R`, one associates
  a Borel measure `f.measure`.
* `f.measure_Ioc` asserts that `f.measure (Ioc a b) = ofReal (f b - f a)`
* `f.measure_Ioo` asserts that `f.measure (Ioo a b) = ofReal (leftLim f b - f a)`.
* `f.measure_Icc` and `f.measure_Ico` are analogous.
* `Monotone.stieltjesFunction`: to a monotone function `f`, associate the Stieltjes function
  equal to the right limit of `f`. This makes it possible to associate a Stieltjes measure to
  any monotone function.

## Implementation

We define Stieltjes functions over any conditionally complete dense linear order, to be able
to cover the cases of `ℝ≥0` and `[0, T]` in addition to the classical case of `ℝ`. This creates
a few issues, mostly with the management of bottom and top elements. To handle these, we need
two technical definitions:
* `Iotop a b` is the interval `Ioo a b` if `b` is not top, and `Ioc a b` if `b` is top.
* `botSet` is the empty set if there is no bot element, and `{x}` if `x` is bot.

Note that the theory of Stieltjes measures is not completely satisfactory when there is a bot
element `x`: any Stieltjes measure gives zero mass to `{x}` in this case, so the Dirac mass at `x`
is not representable as a Stieltjes measure.
-/

noncomputable section

open Set Filter Function ENNReal NNReal Topology MeasureTheory

open ENNReal (ofReal)

section Prerequisites

variable {R : Type*} [LinearOrder R]

open scoped Classical in

def Iotop (a b : R) : Set R := if IsTop b then Ioc a b else Ioo a b

lemma Iotop_subset_Ioc {a b : R} : Iotop a b ⊆ Ioc a b := by
  simp only [Iotop]
  split_ifs with h <;> simp [Ioo_subset_Ioc_self]

lemma Ioo_subset_Iotop {a b : R} : Ioo a b ⊆ Iotop a b := by
  simp only [Iotop]
  split_ifs with h <;> simp [Ioo_subset_Ioc_self]

lemma isOpen_Iotop [TopologicalSpace R] [OrderTopology R] (a b : R) : IsOpen (Iotop a b) := by
  simp only [Iotop]
  split_ifs with h
  · have : Ioc a b = Ioi a := Subset.antisymm (fun x hx ↦ hx.1) (fun x hx ↦ by exact ⟨hx, h _⟩)
    simp [this, isOpen_Ioi]
  · simp [isOpen_Ioo]

open scoped Classical in

def botSet : Set R := {x | IsBot x}
