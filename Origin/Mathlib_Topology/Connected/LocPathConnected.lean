/-
Extracted from Topology/Connected/LocPathConnected.lean
Genuine: 13 of 13 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Locally path-connected spaces

This file defines `LocPathConnectedSpace X`, a predicate class asserting that `X` is locally
path-connected, in that each point has a basis of path-connected neighborhoods.

## Main results

* `IsOpen.pathComponent` / `IsClosed.pathComponent`: in locally path-connected spaces,
  path-components are both open and closed.
* `pathComponent_eq_connectedComponent`: in locally path-connected spaces, path-components and
  connected components agree.
* `pathConnectedSpace_iff_connectedSpace`: locally path-connected spaces are path-connected iff they
  are connected.
* `instLocallyConnectedSpace`: locally path-connected spaces are also locally connected.
* `IsOpen.locPathConnectedSpace`: open subsets of locally path-connected spaces are
  locally path-connected.
* `LocPathConnectedSpace.coinduced` / `Quotient.locPathConnectedSpace`: quotients of locally
  path-connected spaces are locally path-connected.
* `Sum.locPathConnectedSpace` / `Sigma.locPathConnectedSpace`: disjoint unions of locally
  path-connected spaces are locally path-connected.

Abstractly, this also shows that locally path-connected spaces form a coreflective subcategory of
the category of topological spaces, although we do not prove that in this form here.

## Implementation notes

In the definition of `LocPathConnectedSpace X` we require neighbourhoods in the basis to be
path-connected, but not necessarily open; that they can also be required to be open is shown as
a theorem in `isOpen_isPathConnected_basis`.
-/

noncomputable section

open Topology Filter unitInterval Set Function

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x y z : X} {ι : Type*} {F : Set X}

section LocPathConnectedSpace

class LocPathConnectedSpace (X : Type*) [TopologicalSpace X] : Prop where
  /-- Each neighborhood filter has a basis of path-connected neighborhoods. -/
  path_connected_basis : ∀ x : X, (𝓝 x).HasBasis (fun s : Set X => s ∈ 𝓝 x ∧ IsPathConnected s) id

export LocPathConnectedSpace (path_connected_basis)

theorem LocPathConnectedSpace.of_bases {p : X → ι → Prop} {s : X → ι → Set X}
    (h : ∀ x, (𝓝 x).HasBasis (p x) (s x)) (h' : ∀ x i, p x i → IsPathConnected (s x i)) :
    LocPathConnectedSpace X where
  path_connected_basis x := by
    rw [hasBasis_self]
    intro t ht
    rcases (h x).mem_iff.mp ht with ⟨i, hpi, hi⟩
    exact ⟨s x i, (h x).mem_of_mem hpi, h' x i hpi, hi⟩

variable [LocPathConnectedSpace X]

protected theorem IsOpen.pathComponentIn (hF : IsOpen F) (x : X) :
    IsOpen (pathComponentIn F x) := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  let ⟨s, hs⟩ := (path_connected_basis y).mem_iff.mp (hF.mem_nhds (pathComponentIn_subset hy))
  exact mem_of_superset hs.1.1 <| pathComponentIn_congr hy ▸
    hs.1.2.subset_pathComponentIn (mem_of_mem_nhds hs.1.1) hs.2

protected theorem IsOpen.pathComponent (x : X) : IsOpen (pathComponent x) := by
  rw [← pathComponentIn_univ]
  exact isOpen_univ.pathComponentIn _

protected theorem IsClosed.pathComponent (x : X) : IsClosed (pathComponent x) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro y hxy
  rcases (path_connected_basis y).ex_mem with ⟨V, hVy, hVc⟩
  filter_upwards [hVy] with z hz hxz
  exact hxy <| hxz.trans (hVc.joinedIn _ hz _ (mem_of_mem_nhds hVy)).joined

protected theorem IsClopen.pathComponent (x : X) : IsClopen (pathComponent x) :=
  ⟨.pathComponent x, .pathComponent x⟩

lemma pathComponentIn_mem_nhds (hF : F ∈ 𝓝 x) : pathComponentIn F x ∈ 𝓝 x := by
  let ⟨u, huF, hu, hxu⟩ := mem_nhds_iff.mp hF
  exact mem_nhds_iff.mpr ⟨pathComponentIn u x, pathComponentIn_mono huF,
    hu.pathComponentIn x, mem_pathComponentIn_self hxu⟩

theorem PathConnectedSpace.of_locPathConnectedSpace [ConnectedSpace X] : PathConnectedSpace X :=
  ⟨inferInstance, by simp [← mem_pathComponent_iff, IsClopen.pathComponent _ |>.eq_univ]⟩

theorem pathConnectedSpace_iff_connectedSpace : PathConnectedSpace X ↔ ConnectedSpace X :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ .of_locPathConnectedSpace⟩

theorem pathComponent_eq_connectedComponent (x : X) : pathComponent x = connectedComponent x :=
  (pathComponent_subset_component x).antisymm <|
    (IsClopen.pathComponent x).connectedComponent_subset (mem_pathComponent_self _)

theorem connectedComponent_eq_iff_joined (x y : X) :
    connectedComponent x = connectedComponent y ↔ Joined x y := by
  rw [← mem_pathComponent_iff, pathComponent_eq_connectedComponent, eq_comm]
  exact connectedComponent_eq_iff_mem

theorem connectedComponentSetoid_eq_pathSetoid : connectedComponentSetoid X = pathSetoid X :=
  Setoid.ext connectedComponent_eq_iff_joined

def connectedComponentsEquivZerothHomotopy : ConnectedComponents X ≃ ZerothHomotopy X where
  toFun := Quotient.map id (connectedComponent_eq_iff_joined · · |>.mp ·)
  invFun := ZerothHomotopy.toConnectedComponents
  left_inv := Quot.ind <| congrFun rfl
  right_inv := Quot.ind <| congrFun rfl
