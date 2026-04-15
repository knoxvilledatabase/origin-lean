/-
Extracted from Topology/Connected/PathConnected.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Path connectedness

Continuing from `Mathlib/Topology/Path.lean`, this file defines path components and path-connected
spaces.

## Main definitions

In the file the unit interval `[0, 1]` in `ℝ` is denoted by `I`, and `X` is a topological space.

* `Joined (x y : X)` means there is a path between `x` and `y`.
* `Joined.somePath (h : Joined x y)` selects some path between two points `x` and `y`.
* `pathComponent (x : X)` is the set of points joined to `x`.
* `PathConnectedSpace X` is a predicate class asserting that `X` is non-empty and every two
  points of `X` are joined.

Then there are corresponding relative notions for `F : Set X`.

* `JoinedIn F (x y : X)` means there is a path `γ` joining `x` to `y` with values in `F`.
* `JoinedIn.somePath (h : JoinedIn F x y)` selects a path from `x` to `y` inside `F`.
* `pathComponentIn F (x : X)` is the set of points joined to `x` in `F`.
* `IsPathConnected F` asserts that `F` is non-empty and every two
  points of `F` are joined in `F`.

## Main theorems

* `Joined` is an equivalence relation, while `JoinedIn F` is at least symmetric and transitive.

One can link the absolute and relative version in two directions, using `(univ : Set X)` or the
subtype `↥F`.

* `pathConnectedSpace_iff_univ : PathConnectedSpace X ↔ IsPathConnected (univ : Set X)`
* `isPathConnected_iff_pathConnectedSpace : IsPathConnected F ↔ PathConnectedSpace ↥F`

Furthermore, it is shown that continuous images and quotients of path-connected sets/spaces are
path-connected, and that every path-connected set/space is also connected. (See
`Counterexamples.TopologistsSineCurve` for an example of a set in `ℝ × ℝ` that is connected but not
path-connected.)
-/

noncomputable section

open Topology Filter unitInterval Set Function Pointwise Fin

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x y z : X} {ι : Type*}

/-! ### Being joined by a path -/

def Joined (x y : X) : Prop :=
  Nonempty (Path x y)
