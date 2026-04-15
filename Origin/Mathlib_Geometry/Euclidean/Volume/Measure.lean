/-
Extracted from Geometry/Euclidean/Volume/Measure.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Volume measure for Euclidean geometry

In this file we introduce a `d`-dimensional measure for `n`-dimensional Euclidean affine space,
namely `MeasureTheory.Measure.euclideanHausdorffMeasure d` with notation `μHE[d]`.
This is the suitable measure to describe area and volume in an environment of arbitrary dimension.
It is characterized by the following properties:

* Coincides with Lebesgue measure when `d = n`.
* Preserved through isometry, and specifically through affine subspace inclusion.

Internally, this is defined as the `MeasureTheory.Measure.hausdorffMeasure` scaled by a factor.
The factor is defined nonconstructively as the `MeasureTheory.Measure.addHaarScalarFactor` between
the Hausdorff measure and the Lebesgue measure on a model Euclidean space.

TODO: show the scaling factor equals to the ratio between the volume of `d`-dimensional
`Metric.ball` with Euclidean metric and with sup metric.

## Main definitions

* `MeasureTheory.Measure.euclideanHausdorffMeasure`: the Euclidean Hausdorff measure.

## Main statements

* `EuclideanGeometry.measurePreserving_vaddConst`: `μHE[d]` on an affine space matches volume on the
  associated inner product space.
* `AffineSubspace.euclideanHausdorffMeasure_coe_image`: `μHE[d]` is preserved through subspace
  inclusion.

## Tags

Hausdorff measure, measure, metric measure, volume, area
-/

open MeasureTheory Measure Module

-- INSTANCE (free from Core): (d

variable {X Y : Type*}

variable [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]

variable [EMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

noncomputable

def MeasureTheory.Measure.euclideanHausdorffMeasure (d : ℕ) : Measure X :=
  addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin d))) μH[d] • μH[d]
