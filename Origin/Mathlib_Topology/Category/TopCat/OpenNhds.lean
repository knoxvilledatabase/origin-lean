/-
Extracted from Topology/Category/TopCat/OpenNhds.lean
Genuine: 1 of 7 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core

/-!
# The category of open neighborhoods of a point

Given an object `X` of the category `TopCat` of topological spaces and a point `x : X`, this file
builds the type `OpenNhds x` of open neighborhoods of `x` in `X` and endows it with the partial
order given by inclusion and the corresponding category structure (as a full subcategory of the
poset category `Set X`). This is used in `Topology.Sheaves.Stalks` to build the stalk of a sheaf
at `x` as a limit over `OpenNhds x`.

## Main declarations

Besides `OpenNhds`, the main constructions here are:

* `inclusion (x : X)`: the obvious functor `OpenNhds x ⥤ Opens X`
* `functorNhds`: An open map `f : X ⟶ Y` induces a functor `OpenNhds x ⥤ OpenNhds (f x)`
* `adjunctionNhds`: An open map `f : X ⟶ Y` induces an adjunction between `OpenNhds x` and
                    `OpenNhds (f x)`.
-/

open CategoryTheory TopologicalSpace Opposite Topology

universe u

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

namespace TopologicalSpace

def OpenNhds (x : X) : Type u := { U : Opens X // x ∈ U }

namespace OpenNhds

variable {x : X} {U V W : OpenNhds x}

-- INSTANCE (free from Core): partialOrder

-- INSTANCE (free from Core): (x

-- INSTANCE (free from Core): (x

-- INSTANCE (free from Core): (x

-- INSTANCE (free from Core): opensNhds.instFunLike
