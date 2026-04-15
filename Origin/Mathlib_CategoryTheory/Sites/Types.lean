/-
Extracted from CategoryTheory/Sites/Types.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Grothendieck Topology and Sheaves on the Category of Types

In this file we define a Grothendieck topology on the category of types,
and construct the canonical functor that sends a type to a sheaf over
the category of types, and make this an equivalence of categories.

Then we prove that the topology defined is the canonical topology.
-/

universe u

namespace CategoryTheory

def typesGrothendieckTopology : GrothendieckTopology (Type u) where
  sieves α := {S | ∀ x : α, S <| TypeCat.ofHom (fun _ : PUnit => x)}
  top_mem' _ _ := trivial
  pullback_stable' _ _ _ f hs x := hs (f x)
  transitive' _ _ hs _ hr x := hr (hs x) PUnit.unit
