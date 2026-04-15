/-
Extracted from Topology/EMetricSpace/Paracompact.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# (Extended) metric spaces are paracompact

In this file we provide two instances:

* `EMetric.instParacompactSpace`: a `PseudoEMetricSpace` is paracompact; formalization is based
  on [MR0236876];
* `EMetric.instNormalSpace`: an `EMetricSpace` is a normal topological space.

## TODO

Generalize to `PseudoMetrizableSpace`s.

## Tags

metric space, paracompact space, normal space
-/

variable {α : Type*}

open ENNReal Topology Set

namespace Metric

-- INSTANCE (free from Core): (priority

theorem t4Space [EMetricSpace α] : T4Space α := inferInstance

end Metric
