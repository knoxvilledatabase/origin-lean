/-
Extracted from Topology/CWComplex/Classical/Finite.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Finiteness notions on CW complexes

In this file we define what it means for a CW complex to be finite dimensional, of finite type or
finite. We define constructors with relaxed conditions for CW complexes of finite type and
finite CW complexes.

## Main definitions
* `RelCWComplex.FiniteDimensional`: a CW complex is finite dimensional if it has only finitely many
  nonempty indexing types for the cells.
* `RelCWComplex.FiniteType`: a CW complex is of finite type if it has only finitely many cells in
  each dimension.
* `RelCWComplex.Finite`: a CW complex is finite if it is finite dimensional and of finite type.

## Main statements
* `RelCWComplex.mkFiniteType`: if we want to construct a CW complex of finite type, we can relax the
  condition `mapsTo`.
* `RelCWComplex.mkFinite`: if we want to construct a finite CW complex, we can relax the condition
  `mapsTo` and can leave out the condition `closed'`.
* `RelCWComplex.finite_iff_finite_cells`: a CW complex is finite iff the total number of its cells
  is finite.
-/

open Metric Set

namespace Topology

class RelCWComplex.FiniteDimensional.{u} {X : Type u} [TopologicalSpace X] (C : Set X) {D : Set X}
    [RelCWComplex C D] : Prop where
  /-- For some natural number `n`, the type `cell C m` is empty for all `m ≥ n`. -/
  eventually_isEmpty_cell : ∀ᶠ n in Filter.atTop, IsEmpty (cell C n)

class RelCWComplex.FiniteType.{u} {X : Type u} [TopologicalSpace X] (C : Set X) {D : Set X}
    [RelCWComplex C D] : Prop where
  /-- `cell C n` is finite for every `n`. -/
  finite_cell (n : ℕ) : Finite (cell C n)

class RelCWComplex.Finite {X : Type*} [TopologicalSpace X] (C : Set X) {D : Set X}
    [RelCWComplex C D] extends FiniteDimensional C, FiniteType C

variable {X : Type*} [TopologicalSpace X] (C : Set X) {D : Set X} [RelCWComplex C D]

lemma RelCWComplex.finite_of_finiteDimensional_finiteType [FiniteDimensional C]
    [FiniteType C] : Finite C where
  eventually_isEmpty_cell := FiniteDimensional.eventually_isEmpty_cell
  finite_cell n := FiniteType.finite_cell n

namespace CWComplex

export RelCWComplex (FiniteDimensional FiniteType Finite FiniteDimensional.eventually_isEmpty_cell

  FiniteType.finite_cell finite_of_finiteDimensional_finiteType)

end CWComplex
