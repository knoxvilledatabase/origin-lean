/-
Extracted from Topology/OpenPartialHomeomorph/Constructions.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Constructions of new partial homeomorphisms from old

## Main definitions

* `OpenPartialHomeomorph.const`: an open partial homeomorphism which is a constant map,
  whose source and target are necessarily singleton sets
* `OpenPartialHomeomorph.subtypeRestr`: restriction to a subtype
* `OpenPartialHomeomorph.prod`: the product of two open partial homeomorphisms,
  as an open partial homeomorphism on the product space
* `OpenPartialHomeomorph.pi`: the product of a finite family of open partial homeomorphisms
* `OpenPartialHomeomorph.disjointUnion`: combine two open partial homeomorphisms with disjoint
  sources and disjoint targets
* `OpenPartialHomeomorph.lift_openEmbedding`: extend an open partial homeomorphism `X → Y`
  under an open embedding `X → X'`, to an open partial homeomorphism `X' → Z`.
  (This is used to define the disjoint union of charted spaces.)
-/

open Function Set Filter Topology

variable {X X' : Type*} {Y Y' : Type*} {Z Z' : Type*}
  [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y] [TopologicalSpace Y']
  [TopologicalSpace Z] [TopologicalSpace Z']

namespace OpenPartialHomeomorph

variable (e : OpenPartialHomeomorph X Y)

/-!
## Constants

`PartialEquiv.const` as an open partial homeomorphism
-/

section const

variable {a : X} {b : Y}

def const (ha : IsOpen {a}) (hb : IsOpen {b}) : OpenPartialHomeomorph X Y where
  toPartialEquiv := PartialEquiv.single a b
  open_source := ha
  open_target := hb
  continuousOn_toFun := by simp
  continuousOn_invFun := by simp
