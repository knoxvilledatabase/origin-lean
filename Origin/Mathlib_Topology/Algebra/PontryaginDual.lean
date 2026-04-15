/-
Extracted from Topology/Algebra/PontryaginDual.lean
Genuine: 2 of 4 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Pontryagin dual

This file defines the Pontryagin dual of a topological group. The Pontryagin dual of a topological
group `A` is the topological group of continuous homomorphisms `A →* Circle` with the compact-open
topology. For example, `ℤ` and `Circle` are Pontryagin duals of each other. This is an example of
Pontryagin duality, which states that a locally compact abelian topological group is canonically
isomorphic to its double dual.

## Main definitions

* `PontryaginDual A`: The group of continuous homomorphisms `A →* Circle`.
-/

open Pointwise Function

variable (A B C G H : Type*) [Monoid A] [Monoid B] [Monoid C] [CommGroup G] [Group H]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H]

noncomputable section

def PontryaginDual :=
  A →ₜ* Circle

deriving TopologicalSpace

-- INSTANCE (free from Core): [LocallyCompactSpace

variable {A B C G}

namespace PontryaginDual

open ContinuousMonoidHom

#adaptation_note /-- nightly-2026-03-31

Without this `set_option` we get a PANIC!

-/

set_option backward.inferInstanceAs.wrap.data false in

-- INSTANCE (free from Core): :

deriving instance

  T2Space, IsTopologicalGroup,

  Inhabited, FunLike, ContinuousMapClass, MonoidHomClass,

  [DiscreteTopology A] → CompactSpace _

for PontryaginDual A

add_decl_doc instLocallyCompactSpacePontryaginDual

def map (f : A →ₜ* B) :
    (PontryaginDual B) →ₜ* (PontryaginDual A) :=
  f.compLeft Circle
