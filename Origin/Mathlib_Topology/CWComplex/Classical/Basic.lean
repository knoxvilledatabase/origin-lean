/-
Extracted from Topology/CWComplex/Classical/Basic.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# CW complexes

This file defines (relative) CW complexes and proves basic properties about them using the classical
approach of Whitehead.

A CW complex is a topological space that is made by gluing closed disks of different dimensions
together.

## Main definitions
* `RelCWComplex C D`: the class of CW structures on a subspace `C` relative to a base set
  `D` of a topological space `X`.
* `CWComplex C`: an abbreviation for `RelCWComplex C ∅`. The class of CW structures on a
  subspace `C` of the topological space `X`.
* `openCell n`: indexed family of all open cells of dimension `n`.
* `closedCell n`: indexed family of all closed cells of dimension `n`.
* `cellFrontier n`: indexed family of the boundaries of cells of dimension `n`.
* `skeleton C n`: the `n`-skeleton of the (relative) CW complex `C`.

## Main statements
* `iUnion_openCell_eq_skeleton`: the skeletons can also be seen as a union of open cells.
* `cellFrontier_subset_finite_openCell`: the edge of a cell is contained in a finite union of
  open cells of a lower dimension.

## Implementation notes
* We use the historical definition of CW complexes, due to Whitehead: a CW complex is a collection
  of cells with attaching maps - all cells are subspaces of one ambient topological space.
  This way, we avoid having to work with a lot of different topological spaces.
  On the other hand, it requires the union of all cells to be closed.
  If that is not the case, you need to consider that union as a subspace of itself.
* For a categorical approach that defines CW complexes via colimits and transfinite compositions,
  see `Mathlib/Topology/CWComplex/Abstract/Basic.lean`.
  The two approaches are equivalent but serve different purposes:
  * This approach is more convenient for concrete geometric arguments
  * The categorical approach is more suitable for abstract arguments and generalizations
* The definition `RelCWComplex` does not require `X` to be a Hausdorff space.
  A lot of the lemmas will however require this property.
* This definition is a class to ease working with different constructions and their properties.
  Overall this means that being a CW complex is treated more like a property than data.
* The natural number is explicit in `openCell`, `closedCell` and `cellFrontier` because `cell n` and
  `cell m` might be the same type in an explicit CW complex even when `n` and `m` are different.
* `CWComplex` is a separate class from `RelCWComplex`. This not only gives absolute CW complexes a
  better constructor but also aids typeclass inference: a construction on relative CW complexes may
  yield a base that for the special case of CW complexes is provably equal to the empty set but not
  definitionally so. In that case we define an instance specifically for absolute CW complexes and
  want this to be inferred over the relative version. Since the base is an `outParam` this is
  especially necessary since you cannot provide typeclass inference with a specified base.
  But having the type `CWComplex` be separate from `RelCWComplex` makes this specification possible.
* For a similar reason to the previous bullet point we make the instance
  `CWComplex.instRelCWComplex` have high priority. For example, when talking about the type of
  cells `cell C` of an absolute CW complex `C`, this actually refers to `RelCWComplex.cell C`
  through this instance. Again, we want typeclass inference to first consider absolute CW
  structures.
* For statements, the auxiliary construction `skeletonLT` is preferred over `skeleton` as it makes
  the base case of inductions easier. The statement about `skeleton` should then be derived from the
  one about `skeletonLT`.

## References
* [A. Hatcher, *Algebraic Topology*][hatcher02]
-/

noncomputable section

open Metric Set

namespace Topology

class RelCWComplex.{u} {X : Type u} [TopologicalSpace X] (C : Set X) (D : outParam (Set X)) where
  /-- The indexing type of the cells of dimension `n`. -/
  cell (n : ℕ) : Type u
  /-- The characteristic map of the `n`-cell given by the index `i`.
  This map is a bijection when restricting to `ball 0 1`, where we consider `(Fin n → ℝ)`
  endowed with the maximum metric. -/
  map (n : ℕ) (i : cell n) : PartialEquiv (Fin n → ℝ) X
  /-- The source of every characteristic map of dimension `n` is
  `(ball 0 1 : Set (Fin n → ℝ))`. -/
  source_eq (n : ℕ) (i : cell n) : (map n i).source = ball 0 1
  /-- The characteristic maps are continuous when restricting to `closedBall 0 1`. -/
  continuousOn (n : ℕ) (i : cell n) : ContinuousOn (map n i) (closedBall 0 1)
  /-- The inverse of the restriction to `ball 0 1` is continuous on the image. -/
  continuousOn_symm (n : ℕ) (i : cell n) : ContinuousOn (map n i).symm (map n i).target
  /-- The open cells are pairwise disjoint. Use `RelCWComplex.pairwiseDisjoint` or
  `RelCWComplex.disjoint_openCell_of_ne` instead. -/
  pairwiseDisjoint' :
    (univ : Set (Σ n, cell n)).PairwiseDisjoint (fun ni ↦ map ni.1 ni.2 '' ball 0 1)
  /-- All open cells are disjoint with the base. Use `RelCWComplex.disjointBase` instead. -/
  disjointBase' (n : ℕ) (i : cell n) : Disjoint (map n i '' ball 0 1) D
  /-- The boundary of a cell is contained in the union of the base with a finite union of closed
  cells of a lower dimension. Use `RelCWComplex.cellFrontier_subset_base_union_finite_closedCell`
  instead. -/
  mapsTo (n : ℕ) (i : cell n) : ∃ I : Π m, Finset (cell m),
    MapsTo (map n i) (sphere 0 1) (D ∪ ⋃ (m < n) (j ∈ I m), map m j '' closedBall 0 1)
  /-- A CW complex has weak topology, i.e. a set `A` in `X` is closed iff its intersection with
  every closed cell and `D` is closed. Use `RelCWComplex.closed` instead. -/
  closed' (A : Set X) (hAC : A ⊆ C) :
    ((∀ n j, IsClosed (A ∩ map n j '' closedBall 0 1)) ∧ IsClosed (A ∩ D)) → IsClosed A
  /-- The base `D` is closed. -/
  isClosedBase : IsClosed D
  /-- The union of all closed cells equals `C`. Use `RelCWComplex.union` instead. -/
  union' : D ∪ ⋃ (n : ℕ) (j : cell n), map n j '' closedBall 0 1 = C

class CWComplex.{u} {X : Type u} [TopologicalSpace X] (C : Set X) where
  /-- The indexing type of the cells of dimension `n`. -/
  protected cell (n : ℕ) : Type u
  /-- The characteristic map of the `n`-cell given by the index `i`.
  This map is a bijection when restricting to `ball 0 1`, where we consider `(Fin n → ℝ)`
  endowed with the maximum metric. -/
  protected map (n : ℕ) (i : cell n) : PartialEquiv (Fin n → ℝ) X
  /-- The source of every characteristic map of dimension `n` is
  `(ball 0 1 : Set (Fin n → ℝ))`. -/
  protected source_eq (n : ℕ) (i : cell n) : (map n i).source = ball 0 1
  /-- The characteristic maps are continuous when restricting to `closedBall 0 1`. -/
  protected continuousOn (n : ℕ) (i : cell n) : ContinuousOn (map n i) (closedBall 0 1)
  /-- The inverse of the restriction to `ball 0 1` is continuous on the image. -/
  protected continuousOn_symm (n : ℕ) (i : cell n) : ContinuousOn (map n i).symm (map n i).target
  /-- The open cells are pairwise disjoint. Use `CWComplex.pairwiseDisjoint` or
  `CWComplex.disjoint_openCell_of_ne` instead. -/
  protected pairwiseDisjoint' :
    (univ : Set (Σ n, cell n)).PairwiseDisjoint (fun ni ↦ map ni.1 ni.2 '' ball 0 1)
  /-- The boundary of a cell is contained in a finite union of closed cells of a lower dimension.
  Use `CWComplex.mapsTo` or `CWComplex.cellFrontier_subset_finite_closedCell` instead. -/
  protected mapsTo' (n : ℕ) (i : cell n) : ∃ I : Π m, Finset (cell m),
    MapsTo (map n i) (sphere 0 1) (⋃ (m < n) (j ∈ I m), map m j '' closedBall 0 1)
  /-- A CW complex has weak topology, i.e. a set `A` in `X` is closed iff its intersection with
  every closed cell is closed. Use `CWComplex.closed` instead. -/
  protected closed' (A : Set X) (hAC : A ⊆ C) :
    (∀ n j, IsClosed (A ∩ map n j '' closedBall 0 1)) → IsClosed A
  /-- The union of all closed cells equals `C`. Use `CWComplex.union` instead. -/
  protected union' : ⋃ (n : ℕ) (j : cell n), map n j '' closedBall 0 1 = C
