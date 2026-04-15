/-
Extracted from Topology/Defs/Basic.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Basic definitions about topological spaces

This file contains definitions about topology that do not require imports
other than `Mathlib/Data/Set/Lattice.lean`.

## Main definitions

* `TopologicalSpace X`: a typeclass endowing `X` with a topology.
  By definition, a topology is a collection of sets called *open sets* such that

  - `isOpen_univ`: the whole space is open;
  - `IsOpen.inter`: the intersection of two open sets is an open set;
  - `isOpen_sUnion`: the union of a family of open sets is an open set.

* `IsOpen s`: predicate saying that `s` is an open set, same as `TopologicalSpace.IsOpen`.

* `IsClosed s`: a set is called *closed*, if its complement is an open set.
  For technical reasons, this is a typeclass.

* `IsClopen s`: a set is *clopen* if it is both closed and open.

* `interior s`: the *interior* of a set `s` is the maximal open set that is included in `s`.

* `closure s`: the *closure* of a set `s` is the minimal closed set that includes `s`.

* `frontier s`: the *frontier* of a set is the set difference `closure s \ interior s`.
  A point `x` belongs to `frontier s`, if any neighborhood of `x`
  contains points both from `s` and `sᶜ`.

* `Dense s`: a set is *dense* if its closure is the whole space.
  We define it as `∀ x, x ∈ closure s` so that one can write `(h : Dense s) x`.

* `DenseRange f`: a function has *dense range*, if `Set.range f` is a dense set.

* `Continuous f`: a map is *continuous*, if the preimage of any open set is an open set.

* `IsOpenMap f`: a map is an *open map*, if the image of any open set is an open set.

* `IsClosedMap f`: a map is a *closed map*, if the image of any closed set is a closed set.

** Notation

We introduce notation `IsOpen[t]`, `IsClosed[t]`, `closure[t]`, `Continuous[t₁, t₂]`
that allow passing custom topologies to these predicates and functions without using `@`.
-/

assert_not_exists Monoid

universe u v

open Set

class TopologicalSpace (X : Type u) where
  /-- A predicate saying that a set is an open set. Use `IsOpen` in the root namespace instead. -/
  protected IsOpen : Set X → Prop
  /-- The set representing the whole space is an open set.
  Use `isOpen_univ` in the root namespace instead. -/
  protected isOpen_univ : IsOpen univ
  /-- The intersection of two open sets is an open set. Use `IsOpen.inter` instead. -/
  protected isOpen_inter : ∀ s t, IsOpen s → IsOpen t → IsOpen (s ∩ t)
  /-- The union of a family of open sets is an open set.
  Use `isOpen_sUnion` in the root namespace instead. -/
  protected isOpen_sUnion : ∀ s, (∀ t ∈ s, IsOpen t) → IsOpen (⋃₀ s)

variable {X : Type u} {Y : Type v}

/-! ### Predicates on sets -/

section Defs

variable [TopologicalSpace X] [TopologicalSpace Y] {s t : Set X}

def IsOpen : Set X → Prop := TopologicalSpace.IsOpen
