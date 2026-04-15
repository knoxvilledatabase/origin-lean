/-
Extracted from Topology/FiberBundle/IsHomeomorphicTrivialBundle.lean
Genuine: 4 of 8 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core
import Mathlib.Topology.Homeomorph

/-!
# Maps equivariantly-homeomorphic to projection in a product

This file contains the definition `IsHomeomorphicTrivialFiberBundle F p`, a Prop saying that a
map `p : Z → B` between topological spaces is a "trivial fiber bundle" in the sense that there
exists a homeomorphism `h : Z ≃ₜ B × F` such that `proj x = (h x).1`.  This is an abstraction which
is occasionally convenient in showing that a map is open, a quotient map, etc.

This material was formerly linked to the main definition of fiber bundles, but after a series of
refactors, there is no longer a direct connection.
-/

open Topology

variable {B : Type*} (F : Type*) {Z : Type*} [TopologicalSpace B] [TopologicalSpace F]
  [TopologicalSpace Z]

def IsHomeomorphicTrivialFiberBundle (proj : Z → B) : Prop :=
  ∃ e : Z ≃ₜ B × F, ∀ x, (e x).1 = proj x

namespace IsHomeomorphicTrivialFiberBundle

variable {F} {proj : Z → B}

protected theorem proj_eq (h : IsHomeomorphicTrivialFiberBundle F proj) :
    ∃ e : Z ≃ₜ B × F, proj = Prod.fst ∘ e :=
  ⟨h.choose, (funext h.choose_spec).symm⟩

protected theorem surjective_proj [Nonempty F] (h : IsHomeomorphicTrivialFiberBundle F proj) :
    Function.Surjective proj := by
  obtain ⟨e, rfl⟩ := h.proj_eq
  exact Prod.fst_surjective.comp e.surjective

protected theorem continuous_proj (h : IsHomeomorphicTrivialFiberBundle F proj) :
    Continuous proj := by
  obtain ⟨e, rfl⟩ := h.proj_eq; exact continuous_fst.comp e.continuous

protected theorem isOpenMap_proj (h : IsHomeomorphicTrivialFiberBundle F proj) :
    IsOpenMap proj := by
  obtain ⟨e, rfl⟩ := h.proj_eq; exact isOpenMap_fst.comp e.isOpenMap

protected theorem isQuotientMap_proj [Nonempty F] (h : IsHomeomorphicTrivialFiberBundle F proj) :
    IsQuotientMap proj :=
  h.isOpenMap_proj.isQuotientMap h.continuous_proj h.surjective_proj

alias quotientMap_proj := IsHomeomorphicTrivialFiberBundle.isQuotientMap_proj

end IsHomeomorphicTrivialFiberBundle

theorem isHomeomorphicTrivialFiberBundle_fst :
    IsHomeomorphicTrivialFiberBundle F (Prod.fst : B × F → B) :=
  ⟨Homeomorph.refl _, fun _x => rfl⟩

theorem isHomeomorphicTrivialFiberBundle_snd :
    IsHomeomorphicTrivialFiberBundle F (Prod.snd : F × B → B) :=
  ⟨Homeomorph.prodComm _ _, fun _x => rfl⟩
