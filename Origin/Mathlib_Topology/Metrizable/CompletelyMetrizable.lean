/-
Extracted from Topology/Metrizable/CompletelyMetrizable.lean
Genuine: 2 of 4 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Completely (pseudo)metrizable spaces

A topological space is completely (pseudo)metrizable if one can endow it with a
`(Pseudo)MetricSpace` structure which makes it complete and gives the same topology. This typeclass
allows to state theorems which do not require a `(Pseudo)MetricSpace` structure to make sense
without introducing such a structure.
It is in particular useful in measure theory, where one often assumes that a space is a
`PolishSpace`, i.e. a separable and completely metrizable space. Sometimes the separability
hypothesis is not needed and the right assumption is then `IsCompletelyMetrizableSpace`.

## Main definition

* `IsCompletelyPseudoMetrizableSpace X`: A topological space is completely pseudometrizable if
  there exists a pseudometric space structure compatible with the topology which makes the space
  complete. To endow such a space with a compatible distance, use
  `letI := upgradeIsCompletelyPseudoMetrizable X`.

* `IsCompletelyMetrizableSpace X`: A topological space is completely metrizable if
  there exists a metric space structure compatible with the topology which makes the space
  complete. To endow such a space with a compatible distance, use
  `letI := upgradeIsCompletelyMetrizable X`.

## Implementation note

Given a `IsCompletely(Pseudo)MetrizableSpace X` instance, one may want to endow `X` with a complete
(pseudo)metric. This can be done by writing `letI := upgradeIsCompletely(Pseudo)Metrizable X`,
which will endow `X` with an `UpgradedIsCompletely(Pseudo)MetrizableSpace X` instance. This class
is a convenience class and no instance should be registered for it.
-/

open Filter Function Set Topology

variable {X Y : Type*}

namespace TopologicalSpace

class IsCompletelyPseudoMetrizableSpace (X : Type*) [t : TopologicalSpace X] : Prop where
  complete : ∃ m : PseudoMetricSpace X, m.toUniformSpace.toTopologicalSpace = t ∧
    @CompleteSpace X m.toUniformSpace

-- INSTANCE (free from Core): (priority

class UpgradedIsCompletelyPseudoMetrizableSpace (X : Type*) extends
  PseudoMetricSpace X, CompleteSpace X

open scoped Uniformity in

-- INSTANCE (free from Core): (priority
