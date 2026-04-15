/-
Extracted from RingTheory/PowerSeries/Evaluation.lean
Genuine: 11 of 11 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Evaluation of power series

Power series in one indeterminate are the particular case of multivariate power series,
for the `Unit` type of indeterminates.
This file provides a simpler syntax.

Let `R`, `S` be types, with `CommRing R`, `CommRing S`.
One assumes that `IsTopologicalRing R` and `IsUniformAddGroup R`,
and that `S` is a complete and separated topological `R`-algebra,
with `IsLinearTopology S S`, which means there is a basis of neighborhoods of 0
consisting of ideals.

Given `φ : R →+* S`, `a : S`, and `f : MvPowerSeries σ R`,
`PowerSeries.eval₂ f φ a` is the evaluation of the power series `f` at `a`.
It `f` is (the coercion of) a polynomial, it coincides with the evaluation of that polynomial.
Otherwise, it is defined by density from polynomials;
its values are irrelevant unless `φ` is continuous and `a` is topologically
nilpotent (`a ^ n` tends to 0 when `n` tends to infinity).

For consistency with the case of multivariate power series,
we define `PowerSeries.HasEval` as an abbrev to `IsTopologicallyNilpotent`.

Under `Continuous φ` and `HasEval a`,
the following lemmas furnish the properties of evaluation:

* `PowerSeries.eval₂Hom`: the evaluation of multivariate power series, as a ring morphism,
* `PowerSeries.aeval`: the evaluation map as an algebra morphism
* `PowerSeries.uniformContinuous_eval₂`: uniform continuity of the evaluation
* `PowerSeries.continuous_eval₂`: continuity of the evaluation
* `PowerSeries.eval₂_eq_tsum`: the evaluation is given by the sum of its monomials, evaluated.

We refer to the documentation of `MvPowerSeries.eval₂` for more details.

-/

namespace PowerSeries

open WithPiTopology

variable {R : Type*} [CommRing R]

variable {S : Type*} [CommRing S]

variable {φ : R →+* S}

variable [TopologicalSpace R] [TopologicalSpace S]

abbrev HasEval (a : S) := IsTopologicallyNilpotent a

theorem hasEval_def (a : S) : HasEval a ↔ IsTopologicallyNilpotent a := .rfl

theorem hasEval_iff {a : S} :
    HasEval a ↔ MvPowerSeries.HasEval (fun (_ : Unit) ↦ a) :=
  ⟨fun ha ↦ ⟨fun _ ↦ ha, by simp⟩, fun ha ↦ ha.hpow default⟩

theorem hasEval {a : S} (ha : HasEval a) :
    MvPowerSeries.HasEval (fun (_ : Unit) ↦ a) := hasEval_iff.mp ha

theorem HasEval.mono {S : Type*} [CommRing S] {a : S}
    {t u : TopologicalSpace S} (h : t ≤ u) (ha : @HasEval _ _ t a) :
    @HasEval _ _ u a := by
  simp only [hasEval_iff] at ha ⊢
  exact ha.mono h

theorem HasEval.zero : HasEval (0 : S) := by
    rw [hasEval_iff]; exact MvPowerSeries.HasEval.zero

theorem HasEval.add [ContinuousAdd S] [IsLinearTopology S S]
    {a b : S} (ha : HasEval a) (hb : HasEval b) : HasEval (a + b) := by
  simp only [hasEval_iff] at ha hb ⊢
  exact ha.add hb

theorem HasEval.mul_left [IsLinearTopology S S]
    (c : S) {x : S} (hx : HasEval x) : HasEval (c * x) := by
  simp only [hasEval_iff] at hx ⊢
  exact hx.mul_left _

theorem HasEval.mul_right [IsLinearTopology S S]
    (c : S) {x : S} (hx : HasEval x) : HasEval (x * c) := by
  simp only [hasEval_iff] at hx ⊢
  exact hx.mul_right _

theorem HasEval.map (hφ : Continuous φ) {a : R} (ha : HasEval a) :
    HasEval (φ a) := by
  simp only [hasEval_iff] at ha ⊢
  exact ha.map hφ

protected theorem HasEval.X :
    HasEval (X : R⟦X⟧) := by
  rw [hasEval_iff]
  exact MvPowerSeries.HasEval.X

variable [IsTopologicalRing S] [IsLinearTopology S S]
