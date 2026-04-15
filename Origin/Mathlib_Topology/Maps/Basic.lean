/-
Extracted from Topology/Maps/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Specific classes of maps between topological spaces

This file introduces the following properties of a map `f : X → Y` between topological spaces:

* `IsOpenMap f` means the image of an open set under `f` is open.
* `IsClosedMap f` means the image of a closed set under `f` is closed.

(Open and closed maps need not be continuous.)

* `IsInducing f` means the topology on `X` is the one induced via `f` from the topology on `Y`.
  These behave like embeddings except they need not be injective. Instead, points of `X` which
  are identified by `f` are also inseparable in the topology on `X`.
* `IsCoinducing f` means the topology on `Y` is the one coinduced via `f` from the topology on `X`.
* `IsEmbedding f` means `f` is inducing and also injective. Equivalently, `f` identifies `X` with
  a subspace of `Y`.
* `IsOpenEmbedding f` means `f` is an embedding with open image, so it identifies `X` with an
  open subspace of `Y`. Equivalently, `f` is an embedding and an open map.
* `IsClosedEmbedding f` similarly means `f` is an embedding with closed image, so it identifies
  `X` with a closed subspace of `Y`. Equivalently, `f` is an embedding and a closed map.

* `IsQuotientMap f` is the dual condition to `IsEmbedding f`: `f` is surjective and the topology
  on `Y` is the one coinduced via `f` from the topology on `X`. Equivalently, `f` identifies
  `Y` with a quotient of `X`. Quotient maps are also sometimes known as identification maps.

## References

* <https://en.wikipedia.org/wiki/Open_and_closed_maps>
* <https://en.wikipedia.org/wiki/Embedding#General_topology>
* <https://en.wikipedia.org/wiki/Quotient_space_(topology)#Quotient_map>

## Tags

open map, closed map, embedding, quotient map, identification map

-/

open Set Filter Function

open TopologicalSpace Topology Filter

variable {X : Type*} {Y : Type*} {Z : Type*} {ι : Type*} {f : X → Y} {g : Y → Z}

namespace Topology

section IsInducing

variable [TopologicalSpace Y]

protected lemma IsInducing.induced (f : X → Y) : @IsInducing X Y (induced f ‹_›) _ f :=
  @IsInducing.mk _ _ (TopologicalSpace.induced f ‹_›) _ _ rfl

variable [TopologicalSpace X]
