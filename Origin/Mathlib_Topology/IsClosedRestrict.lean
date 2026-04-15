/-
Extracted from Topology/IsClosedRestrict.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Restriction of a closed compact set in a product space to a set of coordinates

We show that the image of a compact closed set `s` in a product `Π i : ι, α i` by
the restriction to a subset of coordinates `S : Set ι` is a closed set.

The idea of the proof is to use `isClosedMap_snd_of_compactSpace`, which is the fact that if
`X` is a compact topological space, then `Prod.snd : X × Y → Y` is a closed map.

We remark that `s` is included in the set `Sᶜ.restrict ⁻¹' (Sᶜ.restrict '' s)`, and we build
a homeomorphism `Sᶜ.restrict ⁻¹' (Sᶜ.restrict '' s) ≃ₜ Sᶜ.restrict '' s × Π i : S, α i`.
`Sᶜ.restrict '' s` is a compact space since `s` is compact, and the lemma applies,
with `X = Sᶜ.restrict '' s` and `Y = Π i : S, α i`.

-/

open Set

variable {ι : Type*} {α : ι → Type*} {s : Set (Π i, α i)} {i : ι} {S : Set ι}

namespace Topology

open Classical in

noncomputable def reorderRestrictProd (S : Set ι) (s : Set (Π j, α j))
    (p : Sᶜ.restrict '' s × (Π i : S, α i)) :
    Π j, α j :=
  fun j ↦ if h : j ∈ S
    then (p.2 : Π j : ↑(S : Set ι), α j) ⟨j, h⟩
    else (p.1 : Π j : ↑(Sᶜ : Set ι), α j) ⟨j, h⟩
