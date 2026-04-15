/-
Extracted from Geometry/Manifold/ContMDiff/Basic.lean
Genuine: 30 | Conflates: 0 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core
import Mathlib.Geometry.Manifold.ContMDiff.Defs

/-!
## Basic properties of smooth functions between manifolds

In this file, we show that standard operations on smooth maps between smooth manifolds are smooth:
* `ContMDiffOn.comp` gives the invariance of the `Cⁿ` property under composition
* `contMDiff_id` gives the smoothness of the identity
* `contMDiff_const` gives the smoothness of constant functions
* `contMDiff_inclusion` shows that the inclusion between open sets of a topological space is smooth
* `contMDiff_isOpenEmbedding` shows that if `M` has a `ChartedSpace` structure induced by an open
embedding `e : M → H`, then `e` is smooth.

## Tags
chain rule, manifolds, higher derivative

-/

open Filter Function Set Topology

open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  -- declare the prerequisites for a charted space `M` over the pair `(E, H)`.
  {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M]
  -- declare the prerequisites for a charted space `M'` over the pair `(E', H')`.
  {E' : Type*}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*} [TopologicalSpace M']
  -- declare the prerequisites for a charted space `M''` over the pair `(E'', H'')`.
  {E'' : Type*}
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] {H'' : Type*} [TopologicalSpace H'']
  {I'' : ModelWithCorners 𝕜 E'' H''} {M'' : Type*} [TopologicalSpace M'']

section ChartedSpace

variable [ChartedSpace H M] [ChartedSpace H' M'] [ChartedSpace H'' M'']
  -- declare functions, sets, points and smoothness indices
  {f : M → M'} {s : Set M} {x : M} {n : ℕ∞}

/-! ### Smoothness of the composition of smooth functions between manifolds -/

section Composition

theorem ContMDiffWithinAt.comp {t : Set M'} {g : M' → M''} (x : M)
    (hg : ContMDiffWithinAt I' I'' n g t (f x)) (hf : ContMDiffWithinAt I I' n f s x)
    (st : MapsTo f s t) : ContMDiffWithinAt I I'' n (g ∘ f) s x := by
  rw [contMDiffWithinAt_iff] at hg hf ⊢
  refine ⟨hg.1.comp hf.1 st, ?_⟩
  set e := extChartAt I x
  set e' := extChartAt I' (f x)
  have : e' (f x) = (writtenInExtChartAt I I' x f) (e x) := by simp only [e, e', mfld_simps]
  rw [this] at hg
  have A : ∀ᶠ y in 𝓝[e.symm ⁻¹' s ∩ range I] e x, f (e.symm y) ∈ t ∧ f (e.symm y) ∈ e'.source := by
    simp only [e, ← map_extChartAt_nhdsWithin, eventually_map]
    filter_upwards [hf.1.tendsto (extChartAt_source_mem_nhds (I := I') (f x)),
      inter_mem_nhdsWithin s (extChartAt_source_mem_nhds (I := I) x)]
    rintro x' (hfx' : f x' ∈ e'.source) ⟨hx's, hx'⟩
    simp only [e.map_source hx', true_and, e.left_inv hx', st hx's, *]
  refine ((hg.2.comp _ (hf.2.mono inter_subset_right)
      ((mapsTo_preimage _ _).mono_left inter_subset_left)).mono_of_mem_nhdsWithin
      (inter_mem ?_ self_mem_nhdsWithin)).congr_of_eventuallyEq ?_ ?_
  · filter_upwards [A]
    rintro x' ⟨ht, hfx'⟩
    simp only [*, mem_preimage, writtenInExtChartAt, (· ∘ ·), mem_inter_iff, e'.left_inv,
      true_and]
    exact mem_range_self _
  · filter_upwards [A]
    rintro x' ⟨-, hfx'⟩
    simp only [*, (· ∘ ·), writtenInExtChartAt, e'.left_inv]
  · simp only [e, e', writtenInExtChartAt, (· ∘ ·), mem_extChartAt_source, e.left_inv, e'.left_inv]

theorem ContMDiffWithinAt.comp_of_eq {t : Set M'} {g : M' → M''} {x : M} {y : M'}
    (hg : ContMDiffWithinAt I' I'' n g t y) (hf : ContMDiffWithinAt I I' n f s x)
    (st : MapsTo f s t) (hx : f x = y) : ContMDiffWithinAt I I'' n (g ∘ f) s x := by
  subst hx; exact hg.comp x hf st

theorem ContMDiffOn.comp {t : Set M'} {g : M' → M''} (hg : ContMDiffOn I' I'' n g t)
    (hf : ContMDiffOn I I' n f s) (st : s ⊆ f ⁻¹' t) : ContMDiffOn I I'' n (g ∘ f) s := fun x hx =>
  (hg _ (st hx)).comp x (hf x hx) st

theorem ContMDiffOn.comp' {t : Set M'} {g : M' → M''} (hg : ContMDiffOn I' I'' n g t)
    (hf : ContMDiffOn I I' n f s) : ContMDiffOn I I'' n (g ∘ f) (s ∩ f ⁻¹' t) :=
  hg.comp (hf.mono inter_subset_left) inter_subset_right

theorem ContMDiff.comp {g : M' → M''} (hg : ContMDiff I' I'' n g) (hf : ContMDiff I I' n f) :
    ContMDiff I I'' n (g ∘ f) := by
  rw [← contMDiffOn_univ] at hf hg ⊢
  exact hg.comp hf subset_preimage_univ

theorem ContMDiffWithinAt.comp' {t : Set M'} {g : M' → M''} (x : M)
    (hg : ContMDiffWithinAt I' I'' n g t (f x)) (hf : ContMDiffWithinAt I I' n f s x) :
    ContMDiffWithinAt I I'' n (g ∘ f) (s ∩ f ⁻¹' t) x :=
  hg.comp x (hf.mono inter_subset_left) inter_subset_right

theorem ContMDiffAt.comp_contMDiffWithinAt {g : M' → M''} (x : M)
    (hg : ContMDiffAt I' I'' n g (f x)) (hf : ContMDiffWithinAt I I' n f s x) :
    ContMDiffWithinAt I I'' n (g ∘ f) s x :=
  hg.comp x hf (mapsTo_univ _ _)

alias SmoothAt.comp_smoothWithinAt := ContMDiffAt.comp_contMDiffWithinAt

nonrec theorem ContMDiffAt.comp {g : M' → M''} (x : M) (hg : ContMDiffAt I' I'' n g (f x))
    (hf : ContMDiffAt I I' n f x) : ContMDiffAt I I'' n (g ∘ f) x :=
  hg.comp x hf (mapsTo_univ _ _)

theorem ContMDiffAt.comp_of_eq {g : M' → M''} {x : M} {y : M'} (hg : ContMDiffAt I' I'' n g y)
    (hf : ContMDiffAt I I' n f x) (hx : f x = y) : ContMDiffAt I I'' n (g ∘ f) x := by
  subst hx; exact hg.comp x hf

theorem ContMDiff.comp_contMDiffOn {f : M → M'} {g : M' → M''} {s : Set M}
    (hg : ContMDiff I' I'' n g) (hf : ContMDiffOn I I' n f s) : ContMDiffOn I I'' n (g ∘ f) s :=
  hg.contMDiffOn.comp hf Set.subset_preimage_univ

theorem ContMDiffOn.comp_contMDiff {t : Set M'} {g : M' → M''} (hg : ContMDiffOn I' I'' n g t)
    (hf : ContMDiff I I' n f) (ht : ∀ x, f x ∈ t) : ContMDiff I I'' n (g ∘ f) :=
  contMDiffOn_univ.mp <| hg.comp hf.contMDiffOn fun x _ => ht x

end Composition

/-! ### The identity is smooth -/

section id

theorem contMDiff_id : ContMDiff I I n (id : M → M) :=
  ContMDiff.of_le
    ((contDiffWithinAt_localInvariantProp ⊤).liftProp_id contDiffWithinAtProp_id) le_top

theorem contMDiffOn_id : ContMDiffOn I I n (id : M → M) s :=
  contMDiff_id.contMDiffOn

theorem contMDiffAt_id : ContMDiffAt I I n (id : M → M) x :=
  contMDiff_id.contMDiffAt

theorem contMDiffWithinAt_id : ContMDiffWithinAt I I n (id : M → M) s x :=
  contMDiffAt_id.contMDiffWithinAt

end id

/-! ### Constants are smooth -/

section id

variable {c : M'}

theorem contMDiff_const : ContMDiff I I' n fun _ : M => c := by
  intro x
  refine ⟨continuousWithinAt_const, ?_⟩
  simp only [ContDiffWithinAtProp, Function.comp_def]
  exact contDiffWithinAt_const

@[to_additive]
theorem contMDiff_one [One M'] : ContMDiff I I' n (1 : M → M') := by
  simp only [Pi.one_def, contMDiff_const]

theorem contMDiffOn_const : ContMDiffOn I I' n (fun _ : M => c) s :=
  contMDiff_const.contMDiffOn

@[to_additive]
theorem contMDiffOn_one [One M'] : ContMDiffOn I I' n (1 : M → M') s :=
  contMDiff_one.contMDiffOn

theorem contMDiffAt_const : ContMDiffAt I I' n (fun _ : M => c) x :=
  contMDiff_const.contMDiffAt

@[to_additive]
theorem contMDiffAt_one [One M'] : ContMDiffAt I I' n (1 : M → M') x :=
  contMDiff_one.contMDiffAt

theorem contMDiffWithinAt_const : ContMDiffWithinAt I I' n (fun _ : M => c) s x :=
  contMDiffAt_const.contMDiffWithinAt

@[to_additive]
theorem contMDiffWithinAt_one [One M'] : ContMDiffWithinAt I I' n (1 : M → M') s x :=
  contMDiffAt_const.contMDiffWithinAt

end id

@[to_additive "`f` is continuously differentiable if it is continuously
differentiable at each `x ∈ tsupport f`."]
theorem contMDiff_of_mulTSupport [One M'] {f : M → M'}
    (hf : ∀ x ∈ mulTSupport f, ContMDiffAt I I' n f x) : ContMDiff I I' n f := by
  intro x
  by_cases hx : x ∈ mulTSupport f
  · exact hf x hx
  · exact ContMDiffAt.congr_of_eventuallyEq contMDiffAt_const
      (not_mem_mulTSupport_iff_eventuallyEq.1 hx)

@[to_additive contMDiffWithinAt_of_not_mem]
theorem contMDiffWithinAt_of_not_mem_mulTSupport {f : M → M'} [One M'] {x : M}
    (hx : x ∉ mulTSupport f) (n : ℕ∞) (s : Set M) : ContMDiffWithinAt I I' n f s x := by
  apply contMDiffWithinAt_const.congr_of_eventuallyEq
    (eventually_nhdsWithin_of_eventually_nhds <| not_mem_mulTSupport_iff_eventuallyEq.mp hx)
    (image_eq_one_of_nmem_mulTSupport hx)

@[to_additive contMDiffAt_of_not_mem]
theorem contMDiffAt_of_not_mem_mulTSupport {f : M → M'} [One M'] {x : M}
    (hx : x ∉ mulTSupport f) (n : ℕ∞) : ContMDiffAt I I' n f x :=
  contMDiffWithinAt_of_not_mem_mulTSupport hx n univ

/-! ### The inclusion map from one open set to another is smooth -/

section Inclusion

open TopologicalSpace

theorem contMDiffAt_subtype_iff {n : ℕ∞} {U : Opens M} {f : M → M'} {x : U} :
    ContMDiffAt I I' n (fun x : U ↦ f x) x ↔ ContMDiffAt I I' n f x :=
  ((contDiffWithinAt_localInvariantProp n).liftPropAt_iff_comp_subtype_val _ _).symm

theorem contMDiff_subtype_val {n : ℕ∞} {U : Opens M} : ContMDiff I I n (Subtype.val : U → M) :=
  fun _ ↦ contMDiffAt_subtype_iff.mpr contMDiffAt_id

@[to_additive]
theorem ContMDiff.extend_one [T2Space M] [One M'] {n : ℕ∞} {U : Opens M} {f : U → M'}
    (supp : HasCompactMulSupport f) (diff : ContMDiff I I' n f) :
    ContMDiff I I' n (Subtype.val.extend f 1) := fun x ↦ by
  refine contMDiff_of_mulTSupport (fun x h ↦ ?_) _
  lift x to U using Subtype.coe_image_subset _ _
    (supp.mulTSupport_extend_one_subset continuous_subtype_val h)
  rw [← contMDiffAt_subtype_iff]
  simp_rw [← comp_def]
  rw [extend_comp Subtype.val_injective]
  exact diff.contMDiffAt

theorem contMDiff_inclusion {n : ℕ∞} {U V : Opens M} (h : U ≤ V) :
    ContMDiff I I n (Opens.inclusion h : U → V) := by
  rintro ⟨x, hx : x ∈ U⟩
  apply (contDiffWithinAt_localInvariantProp n).liftProp_inclusion
  intro y
  dsimp only [ContDiffWithinAtProp, id_comp, preimage_univ]
  rw [Set.univ_inter]
  exact contDiffWithinAt_id.congr I.rightInvOn (congr_arg I (I.left_inv y))

end Inclusion

end ChartedSpace

/-! ### Open embeddings and their inverses are smooth -/

section

variable {e : M → H} (h : IsOpenEmbedding e) {n : WithTop ℕ}

lemma contMDiff_isOpenEmbedding [Nonempty M] :
    haveI := h.singletonChartedSpace; ContMDiff I I n e := by
  haveI := h.singleton_smoothManifoldWithCorners (I := I)
  rw [@contMDiff_iff _ _ _ _ _ _ _ _ _ _ h.singletonChartedSpace]
  use h.continuous
  intros x y
  -- show the function is actually the identity on the range of I ∘ e
  apply contDiffOn_id.congr
  intros z hz
  -- factorise into the chart `e` and the model `id`
  simp only [mfld_simps]
  rw [h.toPartialHomeomorph_right_inv]
  · rw [I.right_inv]
    apply mem_of_subset_of_mem _ hz.1
    exact haveI := h.singletonChartedSpace; extChartAt_target_subset_range (I := I) x
  · -- `hz` implies that `z ∈ range (I ∘ e)`
    have := hz.1
    rw [@extChartAt_target _ _ _ _ _ _ _ _ _ _ h.singletonChartedSpace] at this
    have := this.1
    rw [mem_preimage, PartialHomeomorph.singletonChartedSpace_chartAt_eq,
      h.toPartialHomeomorph_target] at this
    exact this

alias contMDiff_openEmbedding := contMDiff_isOpenEmbedding

lemma contMDiffOn_isOpenEmbedding_symm [Nonempty M] :
    haveI := h.singletonChartedSpace; ContMDiffOn I I
      n (IsOpenEmbedding.toPartialHomeomorph e h).symm (range e) := by
  haveI := h.singleton_smoothManifoldWithCorners (I := I)
  rw [@contMDiffOn_iff]
  constructor
  · rw [← h.toPartialHomeomorph_target]
    exact (h.toPartialHomeomorph e).continuousOn_symm
  · intros z hz
    -- show the function is actually the identity on the range of I ∘ e
    apply contDiffOn_id.congr
    intros z hz
    -- factorise into the chart `e` and the model `id`
    simp only [mfld_simps]
    have : I.symm z ∈ range e := by
      rw [ModelWithCorners.symm, ← mem_preimage]
      exact hz.2.1
    rw [h.toPartialHomeomorph_right_inv e this]
    apply I.right_inv
    exact mem_of_subset_of_mem (extChartAt_target_subset_range _) hz.1

alias contMDiffOn_openEmbedding_symm := contMDiffOn_isOpenEmbedding_symm

variable [ChartedSpace H M]

variable [Nonempty M'] {e' : M' → H'} (h' : IsOpenEmbedding e')

lemma ContMDiff.of_comp_isOpenEmbedding {f : M → M'} (hf : ContMDiff I I' n (e' ∘ f)) :
    haveI := h'.singletonChartedSpace; ContMDiff I I' n f := by
  have : f = (h'.toPartialHomeomorph e').symm ∘ e' ∘ f := by
    ext
    rw [Function.comp_apply, Function.comp_apply, IsOpenEmbedding.toPartialHomeomorph_left_inv]
  rw [this]
  apply @ContMDiffOn.comp_contMDiff _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    h'.singletonChartedSpace _ _ (range e') _ (contMDiffOn_isOpenEmbedding_symm h') hf
  simp

alias ContMDiff.of_comp_openEmbedding := ContMDiff.of_comp_isOpenEmbedding

end
