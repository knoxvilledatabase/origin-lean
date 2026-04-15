/-
Extracted from Topology/VectorBundle/FiniteDimensional.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Finite-rank vector bundles -/

namespace VectorBundle

open Bundle FiberBundle

variable (R : Type*) {B : Type*} (F : Type*) (E : B → Type*)
  [NontriviallyNormedField R] [TopologicalSpace B]
  [TopologicalSpace (TotalSpace F E)]
  [NormedAddCommGroup F] [NormedSpace R F]
  [(x : B) → TopologicalSpace (E x)] [FiberBundle F E]
  [(x : B) → AddCommGroup (E x)] [(x : B) → Module R (E x)] [VectorBundle R F E]

include E F

protected lemma finiteDimensional (b : B) [FiniteDimensional R F] : FiniteDimensional R (E b) :=
  (continuousLinearEquivAt R F E b).symm.finiteDimensional

protected lemma finrank_eq (b : B) : Module.finrank R (E b) = Module.finrank R F :=
  (continuousLinearEquivAt R F E b).finrank_eq

end VectorBundle
