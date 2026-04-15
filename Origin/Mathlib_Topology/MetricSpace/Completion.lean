/-
Extracted from Topology/MetricSpace/Completion.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# The completion of a metric space

Completion of uniform spaces are already defined in `Topology.UniformSpace.Completion`. We show
here that the uniform space completion of a metric space inherits a metric space structure,
by extending the distance to the completion and checking that it is indeed a distance, and that
it defines the same uniformity as the already defined uniform structure on the completion
-/

open Set Filter UniformSpace Metric

open Filter Topology Uniformity

noncomputable section

universe u v

variable {α : Type u} {β : Type v} [PseudoMetricSpace α]

namespace UniformSpace.Completion

-- INSTANCE (free from Core): :

protected theorem uniformContinuous_dist :
    UniformContinuous fun p : Completion α × Completion α ↦ dist p.1 p.2 :=
  uniformContinuous_extension₂ dist

protected theorem continuous_dist [TopologicalSpace β] {f g : β → Completion α} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun x ↦ dist (f x) (g x) :=
  Completion.uniformContinuous_dist.continuous.comp (hf.prodMk hg :)
