/-
Extracted from Topology/Defs/Ultrafilter.lean
Genuine: 1 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Topology.Defs.Basic
import Mathlib.Order.Filter.Ultrafilter
import Mathlib.Data.Set.Lattice
import Mathlib.Topology.Defs.Filter

/-!
# Limit of an ultrafilter.

* `Ultrafilter.lim f`: a limit of an ultrafilter `f`,
  defined as the limit of `(f : Filter X)`
  with a proof of `Nonempty X` deduced from existence of an ultrafilter on `X`.

-/

variable {X : Type*} [TopologicalSpace X]

open Filter

noncomputable nonrec def Ultrafilter.lim (F : Ultrafilter X) : X :=
  @lim X _ (nonempty_of_neBot F) F
