/-
Extracted from Topology/LocallyConstant/Basic.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Locally constant functions

This file sets up the theory of locally constant function from a topological space to a type.

## Main definitions and constructions

* `IsLocallyConstant f` : a map `f : X → Y` where `X` is a topological space is locally
                            constant if every set in `Y` has an open preimage.
* `LocallyConstant X Y` : the type of locally constant maps from `X` to `Y`
* `LocallyConstant.map` : push-forward of locally constant maps
* `LocallyConstant.comap` : pull-back of locally constant maps
-/

variable {X Y Z α : Type*} [TopologicalSpace X]

open Set Filter

open scoped Topology

def IsLocallyConstant (f : X → Y) : Prop :=
  ∀ s : Set Y, IsOpen (f ⁻¹' s)

namespace IsLocallyConstant

open List in

protected theorem tfae (f : X → Y) :
    TFAE [IsLocallyConstant f,
      ∀ x, ∀ᶠ x' in 𝓝 x, f x' = f x,
      ∀ x, IsOpen { x' | f x' = f x },
      ∀ y, IsOpen (f ⁻¹' {y}),
      ∀ x, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∀ x' ∈ U, f x' = f x] := by
  tfae_have 1 → 4 := fun h y => h {y}
  tfae_have 4 → 3 := fun h x => h (f x)
  tfae_have 3 → 2 := fun h x => IsOpen.mem_nhds (h x) rfl
  tfae_have 2 → 5
  | h, x => by
    rcases mem_nhds_iff.1 (h x) with ⟨U, eq, hU, hx⟩
    exact ⟨U, hU, hx, eq⟩
  tfae_have 5 → 1
  | h, s => by
    refine isOpen_iff_forall_mem_open.2 fun x hx ↦ ?_
    rcases h x with ⟨U, hU, hxU, eq⟩
    exact ⟨U, fun x' hx' => mem_preimage.2 <| (eq x' hx').symm ▸ hx, hU, hxU⟩
  tfae_finish
