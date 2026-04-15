/-
Extracted from Analysis/Convex/GaugeRescale.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# "Gauge rescale" homeomorphism between convex sets

Given two convex von Neumann bounded neighbourhoods of the origin
in a real topological vector space,
we construct a homeomorphism `gaugeRescaleHomeomorph`
that sends the interior, the closure, and the frontier of one set
to the interior, the closure, and the frontier of the other set.
-/

open Metric Bornology Filter Set

open scoped NNReal Topology Pointwise

noncomputable section

section Module

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def gaugeRescale (s t : Set E) (x : E) : E := (gauge s x / gauge t x) • x
