/-
Extracted from MeasureTheory/Measure/WithDensityFinite.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# s-finite measures can be written as `withDensity` of a finite measure

If `μ` is an s-finite measure, then there exists a finite measure `μ.toFinite`
such that a set is `μ`-null iff it is `μ.toFinite`-null.
In particular, `MeasureTheory.ae μ.toFinite = MeasureTheory.ae μ` and `μ.toFinite = 0` iff `μ = 0`.
As a corollary, `μ` can be represented as `μ.toFinite.withDensity (μ.rnDeriv μ.toFinite)`.

Our definition of `MeasureTheory.Measure.toFinite` ensures some extra properties:

- if `μ` is a finite measure, then `μ.toFinite = μ[|univ] = (μ univ)⁻¹ • μ`;
- in particular, `μ.toFinite = μ` for a probability measure;
- if `μ ≠ 0`, then `μ.toFinite` is a probability measure.

## Main definitions

In this definition and the results below, `μ` is an s-finite measure (`SFinite μ`).

* `MeasureTheory.Measure.toFinite`: a finite measure with `μ ≪ μ.toFinite` and `μ.toFinite ≪ μ`.
  If `μ ≠ 0`, this is a probability measure.

## Main statements

* `absolutelyContinuous_toFinite`: `μ ≪ μ.toFinite`.
* `toFinite_absolutelyContinuous`: `μ.toFinite ≪ μ`.
* `ae_toFinite`: `ae μ.toFinite = ae μ`.

-/

open Set

open scoped ENNReal ProbabilityTheory

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}

noncomputable def Measure.toFiniteAux (μ : Measure α) [SFinite μ] : Measure α :=
  letI := Classical.dec
  if IsFiniteMeasure μ then μ else (exists_isFiniteMeasure_absolutelyContinuous μ).choose

noncomputable def Measure.toFinite (μ : Measure α) [SFinite μ] : Measure α :=
  μ.toFiniteAux[|univ]
