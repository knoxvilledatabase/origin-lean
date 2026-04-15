/-
Extracted from Geometry/Manifold/IsManifold/InteriorBoundary.lean
Genuine: 37 of 63 | Dissolved: 19 | Infrastructure: 7
-/
import Origin.Core

/-!
# Interior and boundary of a manifold
Define the interior and boundary of a manifold.

## Main definitions
- **IsInteriorPoint x**: `x ∈ M` is an interior point if, with `φ` being the preferred chart at `x`,
  `φ x` is an interior point of `φ.target`.
- **IsBoundaryPoint x**: `x ∈ M` is a boundary point if `(extChartAt I x) x ∈ frontier (range I)`.
- **interior I M** is the **interior** of `M`, the set of its interior points.
- **boundary I M** is the **boundary** of `M`, the set of its boundary points.

## Main results
- `ModelWithCorners.univ_eq_interior_union_boundary`: `M` is the union of its interior and boundary
- `ModelWithCorners.interior_boundary_disjoint`: interior and boundary of `M` are disjoint
- `BoundarylessManifold.isInteriorPoint`: if `M` is boundaryless, every point is an interior point
- `ModelWithCorners.Boundaryless.boundary_eq_empty` and `of_boundary_eq_empty`:
  `M` is boundaryless if and only if its boundary is empty

- `isInteriorPoint_iff_of_mem_atlas`: a point is an interior point iff any given chart around it
  sends it to the interior of the model; that is, the notion of interior is independent of choices
  of charts
- `ModelWithCorners.isOpen_interior`, `ModelWithCorners.isClosed_boundary`: the interior is open and
  and the boundary is closed. This is currently only proven for C¹ manifolds.

- `MDifferentiableAt.isInteriorPoint_of_surjective_mfderiv`: differentiable maps with surjective
  differential send interior points to interior points
- `IsLocalDiffeomorphAt.isInteriorPoint_iff` etc.: local diffeomorphisms preserve both the boundary
  and interior

- `ModelWithCorners.interior_open`: the interior of `u : Opens M` is the preimage of the interior
  of `M` under the inclusion
- `ModelWithCorners.boundary_open`: the boundary of `u : Opens M` is the preimage of the boundary
  of `M` under the inclusion
- `ModelWithCorners.BoundarylessManifold.open`: if `M` is boundaryless, so is `u : Opens M`

- `ModelWithCorners.interior_prod`: the interior of `M × N` is the product of the interiors
  of `M` and `N`.
- `ModelWithCorners.boundary_prod`: the boundary of `M × N` is `∂M × N ∪ (M × ∂N)`.
- `ModelWithCorners.BoundarylessManifold.prod`: if `M` and `N` are boundaryless, so is `M × N`

- `ModelWithCorners.interior_disjointUnion`: the interior of a disjoint union `M ⊔ M'`
  is the union of the interior of `M` and `M'`
- `ModelWithCorners.boundary_disjointUnion`: the boundary of a disjoint union `M ⊔ M'`
  is the union of the boundaries of `M` and `M'`
- `ModelWithCorners.boundaryless_disjointUnion`: if `M` and `M'` are boundaryless,
  so is their disjoint union `M ⊔ M'`

## Tags
manifold, interior, boundary

## TODO
- the interior of `M` is dense, the boundary nowhere dense
- the interior of `M` is a boundaryless manifold
- `boundary M` is a submanifold (possibly with boundary and corners):
  follows from the corresponding statement for the model with corners `I`;
  this requires a definition of submanifolds
- if `M` is finite-dimensional, its boundary has measure zero
- generalise lemmas about C¹ manifolds with boundary to also hold for finite-dimensional topological
  manifolds; this will require e.g. the homology of spheres.
- submersions send interior points to interior points. This should be an easy consequence of
  `MDifferentiableAt.isInteriorPoint_of_surjective_mfderiv` once submersions are defined.

-/

open Set Function

open scoped Topology Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

namespace ModelWithCorners

variable (I) in

def IsInteriorPoint (x : M) := extChartAt I x x ∈ interior (range I)

variable (I) in

def IsBoundaryPoint (x : M) := extChartAt I x x ∈ frontier (range I)

variable (M) in

protected def interior : Set M := { x : M | I.IsInteriorPoint x }

lemma isInteriorPoint_iff {x : M} :
    I.IsInteriorPoint x ↔ extChartAt I x x ∈ interior (extChartAt I x).target :=
  ⟨fun h ↦ (chartAt H x).mem_interior_extend_target (mem_chart_target H x) h,
    fun h ↦ OpenPartialHomeomorph.interior_extend_target_subset_interior_range _ h⟩

variable (M) in

protected def boundary : Set M := { x : M | I.IsBoundaryPoint x }

lemma isInteriorPoint_or_isBoundaryPoint (x : M) : I.IsInteriorPoint x ∨ I.IsBoundaryPoint x := by
  rw [IsInteriorPoint, or_iff_not_imp_left, I.isBoundaryPoint_iff, ← closure_diff_interior,
    I.isClosed_range.closure_eq, mem_diff]
  exact fun h ↦ ⟨mem_range_self _, h⟩

lemma interior_union_boundary_eq_univ : (I.interior M) ∪ (I.boundary M) = (univ : Set M) :=
  eq_univ_of_forall fun x => (mem_union _ _ _).mpr (I.isInteriorPoint_or_isBoundaryPoint x)

lemma disjoint_interior_boundary : Disjoint (I.interior M) (I.boundary M) := by
  by_contra h
  -- Choose some x in the intersection of interior and boundary.
  obtain ⟨x, h1, h2⟩ := not_disjoint_iff.mp h
  rw [← mem_empty_iff_false (extChartAt I x x),
    ← disjoint_iff_inter_eq_empty.mp disjoint_interior_frontier, mem_inter_iff]
  exact ⟨h1, h2⟩

lemma isInteriorPoint_iff_not_isBoundaryPoint (x : M) :
    I.IsInteriorPoint x ↔ ¬I.IsBoundaryPoint x := by
  refine ⟨?_,
    by simpa only [or_iff_not_imp_right] using isInteriorPoint_or_isBoundaryPoint x (I := I)⟩
  by_contra! h
  rw [← mem_empty_iff_false (extChartAt I x x),
    ← disjoint_iff_inter_eq_empty.mp disjoint_interior_frontier, mem_inter_iff]
  exact h

lemma isBoundaryPoint_iff_not_isInteriorPoint (x : M) :
    I.IsBoundaryPoint x ↔ ¬I.IsInteriorPoint x := by
  simp [isInteriorPoint_iff_not_isBoundaryPoint]

lemma compl_interior : (I.interior M)ᶜ = I.boundary M := by
  apply compl_unique ?_ I.interior_union_boundary_eq_univ
  exact disjoint_iff_inter_eq_empty.mp I.disjoint_interior_boundary

lemma compl_boundary : (I.boundary M)ᶜ = I.interior M := by
  rw [← compl_interior, compl_compl]

lemma _root_.range_mem_nhds_isInteriorPoint {x : M} (h : I.IsInteriorPoint x) :
    range I ∈ 𝓝 (extChartAt I x x) := by
  rw [mem_nhds_iff]
  exact ⟨interior (range I), interior_subset, isOpen_interior, h⟩

class _root_.BoundarylessManifold {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] : Prop where
  isInteriorPoint' : ∀ x : M, IsInteriorPoint I x

section Boundaryless

variable [I.Boundaryless]

-- INSTANCE (free from Core): :

end Boundaryless

section BoundarylessManifold

-- INSTANCE (free from Core): BoundarylessManifold.of_empty

lemma _root_.BoundarylessManifold.isInteriorPoint {x : M} [BoundarylessManifold I M] :
    IsInteriorPoint I x := BoundarylessManifold.isInteriorPoint' x

lemma interior_eq_univ [BoundarylessManifold I M] : I.interior M = univ :=
  eq_univ_of_forall fun _ => BoundarylessManifold.isInteriorPoint

lemma Boundaryless.boundary_eq_empty [BoundarylessManifold I M] : I.boundary M = ∅ := by
  rw [← I.compl_interior, I.interior_eq_univ, compl_empty_iff]

-- INSTANCE (free from Core): [BoundarylessManifold

lemma Boundaryless.iff_boundary_eq_empty : I.boundary M = ∅ ↔ BoundarylessManifold I M := by
  refine ⟨fun h ↦ { isInteriorPoint' := ?_ }, fun a ↦ boundary_eq_empty⟩
  intro x
  change x ∈ I.interior M
  rw [← compl_interior, compl_empty_iff] at h
  rw [h]
  trivial

lemma Boundaryless.of_boundary_eq_empty (h : I.boundary M = ∅) : BoundarylessManifold I M :=
  (Boundaryless.iff_boundary_eq_empty (I := I)).mp h

end BoundarylessManifold

section ChartIndependence

lemma _root_.DifferentiableAt.mem_interior_convex_of_surjective_fderiv
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup H] [NormedSpace ℝ H]
    {f : E → H} {x : E} (hf : DifferentiableAt ℝ f x) {u : Set E} (hu : u ∈ 𝓝 x) {s : Set H}
    (hs : Convex ℝ s) (hs' : IsClosed s) (hs'' : (interior s).Nonempty) (hfus : Set.MapsTo f u s)
    (hfx : Function.Surjective (fderiv ℝ f x)) : f x ∈ interior s := by
  contrapose hfx
  have ⟨F, hF⟩ := geometric_hahn_banach_open_point hs.interior isOpen_interior hfx
  -- It suffices to show that `fderiv ℝ f x` sends everything to the kernel of `F`.
  suffices h : ∀ y, F (fderiv ℝ f x y) = 0 by
    have ⟨y, hy⟩ := hs''
    unfold Function.Surjective; push Not
    refine ⟨f x - y, fun z ↦ ne_of_apply_ne F ?_⟩
    rw [h z, F.map_sub]
    exact (sub_pos.2 <| hF _ hy).ne
  -- This follows from `F ∘ f` taking on a local maximum at `e.extend I x`.
  have hF' : MapsTo F s (Iic (F (f x))) := by
    rw [← hs'.closure_eq, ← closure_Iio, ← hs.closure_interior_eq_closure_of_nonempty_interior hs'']
    exact .closure hF F.continuous
  have hFφ : IsLocalMax (F ∘ f) x := Filter.eventually_of_mem hu fun y hy ↦ hF' <| hfus hy
  have h := hFφ.fderiv_eq_zero
  rw [fderiv_comp _ (by fun_prop) hf, ContinuousLinearMap.fderiv] at h
  exact DFunLike.congr_fun h

variable {n : WithTop ℕ∞} [IsManifold I n M] {e e' : OpenPartialHomeomorph M H} {x : M}

-- DISSOLVED: mem_interior_range_of_mem_interior_range_of_mem_atlas

-- DISSOLVED: mem_interior_range_iff_of_mem_atlas

-- DISSOLVED: isInteriorPoint_iff_of_mem_atlas

-- DISSOLVED: isBoundaryPoint_iff_of_mem_atlas

-- DISSOLVED: isOpen_interior

-- DISSOLVED: isClosed_boundary

end ChartIndependence

end ModelWithCorners

/-! Interior and boundary are preserved under (local) diffeomorphisms. -/

section Diffeomorph

open ModelWithCorners

variable
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {n : WithTop ℕ∞}

lemma MDifferentiableAt.isInteriorPoint_of_surjective_mfderiv {f : M → N} {x : M}
    (hf : MDifferentiableAt I I' f x) (hf' : Surjective (mfderiv I I' f x))
    (hx : I.IsInteriorPoint x) : I'.IsInteriorPoint (f x) := by
  -- Since p-adic manifolds don't have boundary, WLOG `𝕜` is `ℝ` or `ℂ` and `E` is normed over `ℝ`.
  wlog _ : IsRCLikeNormedField 𝕜
  · simp [IsInteriorPoint, I'.range_eq_univ_of_not_isRCLikeNormedField ‹_›]
  let _ := IsRCLikeNormedField.rclike 𝕜
  let _ : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  let _ : NormedSpace ℝ E' := NormedSpace.restrictScalars ℝ 𝕜 E'
  -- Write everything in terms of extended charts around `x` and `f x`.
  simp only [mfderiv, hf, ite_true] at hf'
  have hf'' := hf.differentiableWithinAt_writtenInExtChartAt.differentiableAt <| by
    simpa [← mem_interior_iff_mem_nhds] using hx
  rw [fderivWithin_eq_fderiv (I.uniqueDiffOn _ <| by simp) hf''] at hf'
  /- Since `writtenInExtChartAt I I' x f` is differentiable with surjective differential at `x`
  over `𝕜`, it also is so over `ℝ`. -/
  replace hf' : Surjective (fderiv ℝ (writtenInExtChartAt I I' x f) (extChartAt I x x)) := by
    rwa [hf''.fderiv_restrictScalars (𝕜 := ℝ), ContinuousLinearMap.coe_restrictScalars']
  replace hf'' := hf''.restrictScalars ℝ
  /- The lemma is now essentially just `mem_interior_convex_of_surjective_fderiv`: because
  `writtenInExtChartAt I I' x f` is differentiable with surjective differential at `x` over `ℝ` and
  sends a neighbourhood of `x` (the region in which it could be written in the extended charts) to
  a closed convex set with nonempty interior (`I'.range`), it must send `x` to that interior. -/
  have := hf''.mem_interior_convex_of_surjective_fderiv (Filter.inter_mem ?_ ?_) I'.convex_range
    I'.isClosed_range I'.nonempty_interior (writtenInExtChartAt_mapsTo.mono_right ?_) hf'
  · simpa using this
  · rw [← nhdsWithin_eq_nhds.2 (mem_interior_iff_mem_nhds.1 hx)]
    exact extChartAt_target_mem_nhdsWithin x
  · exact extChartAt_preimage_mem_nhds <| hf.continuousAt.preimage_mem_nhds <|
      extChartAt_source_mem_nhds _
  · exact extChartAt_target_subset_range _

-- DISSOLVED: IsLocalDiffeomorphAt.isInteriorPoint_iff

-- DISSOLVED: IsLocalDiffeomorphAt.isBoundaryPoint_iff

-- DISSOLVED: IsLocalDiffeomorphOn.preimage_interior_inter

-- DISSOLVED: IsLocalDiffeomorphOn.preimage_boundary_inter

-- DISSOLVED: IsLocalDiffeomorph.preimage_interior

-- DISSOLVED: IsLocalDiffeomorph.preimage_boundary

-- DISSOLVED: IsLocalDiffeomorph.boundarylessManifold

-- DISSOLVED: Diffeomorph.preimage_interior

-- DISSOLVED: Diffeomorph.preimage_boundary

-- DISSOLVED: Diffeomorph.image_interior

-- DISSOLVED: Diffeomorph.image_boundary

-- DISSOLVED: Diffeomorph.boundarylessManifold

-- DISSOLVED: Diffeomorph.boundarylessManifold_iff

end Diffeomorph

namespace ModelWithCorners

/-! Interior and boundary of open subsets of a manifold. -/

section opens

open TopologicalSpace

lemma isInteriorPoint_iff_isInteriorPoint_val {u : Opens M} {x : u} :
    I.IsInteriorPoint x ↔ I.IsInteriorPoint x.1 := by
  simpa [I.isInteriorPoint_iff, u.chartAt_eq,
    OpenPartialHomeomorph.subtypeRestr, mem_interior_iff_mem_nhds] using
    fun _ _ ↦ (chartAt H x.1).extend_preimage_mem_nhds (mem_chart_source H x.1) (u.2.mem_nhds x.2)

lemma isBoundaryPoint_iff_isBoundaryPoint_val {u : Opens M} {x : u} :
    I.IsBoundaryPoint x ↔ I.IsBoundaryPoint x.1 := by
  simpa [I.isInteriorPoint_iff_not_isBoundaryPoint, not_iff_not] using
    I.isInteriorPoint_iff_isInteriorPoint_val

lemma interior_open {u : Opens M} : I.interior u = (↑) ⁻¹' I.interior M := by
  ext1; exact I.isInteriorPoint_iff_isInteriorPoint_val

lemma boundary_open {u : Opens M} : I.boundary u = (↑) ⁻¹' I.boundary M := by
  simp [← I.compl_interior, I.interior_open]

-- INSTANCE (free from Core): BoundarylessManifold.open

end opens

/-! Interior and boundary of the product of two manifolds. -/

section prod

variable
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H']
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {J : ModelWithCorners 𝕜 E' H'} {x : M} {y : N}

set_option backward.isDefEq.respectTransparency false in

lemma interior_prod :
    (I.prod J).interior (M × N) = (I.interior M) ×ˢ (J.interior N) := by
  ext p
  have aux : (interior (range ↑I)) ×ˢ (interior (range J)) = interior (range (I.prod J)) := by
    rw [← interior_prod_eq, ← range_prodMap, modelWithCorners_prod_coe]
  constructor <;> intro hp
  · replace hp : (I.prod J).IsInteriorPoint p := hp
    rw [IsInteriorPoint, ← aux] at hp
    exact hp
  · change (I.prod J).IsInteriorPoint p
    rw [IsInteriorPoint, ← aux, mem_prod]
    obtain h := Set.mem_prod.mp hp
    rw [ModelWithCorners.interior] at h
    exact h

lemma boundary_prod :
    (I.prod J).boundary (M × N) = Set.prod univ (J.boundary N) ∪ Set.prod (I.boundary M) univ := by
  let h := calc (I.prod J).boundary (M × N)
    _ = ((I.prod J).interior (M × N))ᶜ := compl_interior.symm
    _ = ((I.interior M) ×ˢ (J.interior N))ᶜ := by rw [interior_prod]
    _ = (I.interior M)ᶜ ×ˢ univ ∪ univ ×ˢ (J.interior N)ᶜ := by rw [compl_prod_eq_union]
  rw [h, I.compl_interior, J.compl_interior, union_comm]
  rfl

lemma boundary_of_boundaryless_left [BoundarylessManifold I M] :
    (I.prod J).boundary (M × N) = Set.prod (univ : Set M) (J.boundary N) := by
  rw [boundary_prod, Boundaryless.boundary_eq_empty (I := I)]
  have : Set.prod (∅ : Set M) (univ : Set N) = ∅ := Set.empty_prod
  rw [this, union_empty]

lemma boundary_of_boundaryless_right [BoundarylessManifold J N] :
    (I.prod J).boundary (M × N) = Set.prod (I.boundary M) (univ : Set N) := by
  rw [boundary_prod, Boundaryless.boundary_eq_empty (I := J)]
  have : Set.prod (univ : Set M) (∅ : Set N) = ∅ := Set.prod_empty
  rw [this, empty_union]

-- INSTANCE (free from Core): BoundarylessManifold.prod

end prod

/-! Interior and boundary of the disjoint union of two manifolds. -/

section disjointUnion

variable {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M'] {n : WithTop ℕ∞}

open Topology

lemma interiorPoint_inl (x : M) (hx : I.IsInteriorPoint x) :
    I.IsInteriorPoint (.inl x : M ⊕ M') := by
  rw [I.isInteriorPoint_iff, extChartAt, ChartedSpace.sum_chartAt_inl]
  dsimp
  rw [Sum.inl_injective.extend_apply (chartAt H x)]
  simpa [I.isInteriorPoint_iff, extChartAt] using hx

lemma boundaryPoint_inl (x : M) (hx : I.IsBoundaryPoint x) :
    I.IsBoundaryPoint (.inl x : M ⊕ M') := by
  rw [I.isBoundaryPoint_iff, extChartAt, ChartedSpace.sum_chartAt_inl]
  dsimp
  rw [Sum.inl_injective.extend_apply (chartAt H x)]
  simpa [I.isBoundaryPoint_iff, extChartAt] using hx

lemma interiorPoint_inr (x : M') (hx : I.IsInteriorPoint x) :
    I.IsInteriorPoint (.inr x : M ⊕ M') := by
  rw [I.isInteriorPoint_iff, extChartAt, ChartedSpace.sum_chartAt_inr]
  dsimp
  rw [Sum.inr_injective.extend_apply (chartAt H x)]
  simpa [I.isInteriorPoint_iff, extChartAt] using hx

lemma boundaryPoint_inr (x : M') (hx : I.IsBoundaryPoint x) :
    I.IsBoundaryPoint (.inr x : M ⊕ M') := by
  rw [I.isBoundaryPoint_iff, extChartAt, ChartedSpace.sum_chartAt_inr]
  dsimp
  rw [Sum.inr_injective.extend_apply (chartAt H x)]
  simpa [I.isBoundaryPoint_iff, extChartAt] using hx

lemma isInteriorPoint_disjointUnion_left {p : M ⊕ M'} (hp : I.IsInteriorPoint p)
    (hleft : Sum.isLeft p) : I.IsInteriorPoint (Sum.getLeft p hleft) := by
  grind [isInteriorPoint_iff_not_isBoundaryPoint, boundaryPoint_inl]

lemma isInteriorPoint_disjointUnion_right {p : M ⊕ M'} (hp : I.IsInteriorPoint p)
    (hright : Sum.isRight p) : I.IsInteriorPoint (Sum.getRight p hright) := by
  grind [isInteriorPoint_iff_not_isBoundaryPoint, boundaryPoint_inr]

lemma interior_disjointUnion :
    ModelWithCorners.interior (I := I) (M ⊕ M') =
      Sum.inl '' (ModelWithCorners.interior (I := I) M)
      ∪ Sum.inr '' (ModelWithCorners.interior (I := I) M') := by
  grind [boundaryPoint_inl, boundaryPoint_inr, interior.eq_def, interiorPoint_inl,
    interiorPoint_inr, isInteriorPoint_iff_not_isBoundaryPoint]

lemma boundary_disjointUnion : ModelWithCorners.boundary (I := I) (M ⊕ M') =
      Sum.inl '' (ModelWithCorners.boundary (I := I) M)
      ∪ Sum.inr '' (ModelWithCorners.boundary (I := I) M') := by
  simp only [← ModelWithCorners.compl_interior, interior_disjointUnion, inl_compl_union_inr_compl]

-- INSTANCE (free from Core): boundaryless_disjointUnion

end disjointUnion

end ModelWithCorners
