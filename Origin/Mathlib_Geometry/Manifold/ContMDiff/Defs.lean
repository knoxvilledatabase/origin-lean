/-
Extracted from Geometry/Manifold/ContMDiff/Defs.lean
Genuine: 16 of 19 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# `C^n` functions between manifolds

We define `Cⁿ` functions between manifolds, as functions which are `Cⁿ` in charts, and prove
basic properties of these notions. Here, `n` can be finite, or `∞`, or `ω`.

## Main definitions and statements

Let `M` and `M'` be two manifolds, with respect to models with corners `I` and `I'`. Let
`f : M → M'`.

* `ContMDiffWithinAt I I' n f s x` states that the function `f` is `Cⁿ` within the set `s`
  around the point `x`.
* `ContMDiffAt I I' n f x` states that the function `f` is `Cⁿ` around `x`.
* `ContMDiffOn I I' n f s` states that the function `f` is `Cⁿ` on the set `s`
* `ContMDiff I I' n f` states that the function `f` is `Cⁿ`.

We also give some basic properties of `Cⁿ` functions between manifolds, following the API of
`C^n` functions between vector spaces.
See `Basic.lean` for further basic properties of `Cⁿ` functions between manifolds,
`NormedSpace.lean` for the equivalence of manifold-smoothness to usual smoothness,
`Product.lean` for smoothness results related to the product of manifolds and
`Atlas.lean` for smoothness of atlas members and local structomorphisms.

## Implementation details

Many properties follow for free from the corresponding properties of functions in vector spaces,
as being `Cⁿ` is a local property invariant under the `Cⁿ` groupoid. We take advantage of the
general machinery developed in `LocalInvariantProperties.lean` to get these properties
automatically. For instance, the fact that being `Cⁿ` does not depend on the chart one considers
is given by `liftPropWithinAt_indep_chart`.

For this to work, the definition of `ContMDiffWithinAt` and friends has to
follow definitionally the setup of local invariant properties. Still, we recast the definition
in terms of extended charts in `contMDiffOn_iff` and `contMDiff_iff`.
-/

open Set Function Filter ChartedSpace IsManifold

open scoped Topology Manifold ContDiff

/-! ### Definition of `Cⁿ` functions between manifolds -/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  -- Prerequisite typeclasses to say that `M` is a manifold over the pair `(E, H)`
  {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  -- Prerequisite typeclasses to say that `M'` is a manifold over the pair `(E', H')`
  {E' : Type*}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  -- Prerequisite typeclasses to say that `M''` is a manifold over the pair `(E'', H'')`
  {E'' : Type*}
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] {H'' : Type*} [TopologicalSpace H'']
  {I'' : ModelWithCorners 𝕜 E'' H''} {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M'']
  -- declare functions, sets, points and smoothness indices
  {e : OpenPartialHomeomorph M H}
  {e' : OpenPartialHomeomorph M' H'} {f f₁ : M → M'} {s s₁ t : Set M} {x : M} {m n : WithTop ℕ∞}

variable (I I') in

def ContDiffWithinAtProp (n : WithTop ℕ∞) (f : H → H') (s : Set H) (x : H) : Prop :=
  ContDiffWithinAt 𝕜 n (I' ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ range I) (I x)

theorem contDiffWithinAtProp_self_source {f : E → H'} {s : Set E} {x : E} :
    ContDiffWithinAtProp 𝓘(𝕜, E) I' n f s x ↔ ContDiffWithinAt 𝕜 n (I' ∘ f) s x := by
  simp_rw [ContDiffWithinAtProp, modelWithCornersSelf_coe, range_id, inter_univ,
    modelWithCornersSelf_coe_symm, CompTriple.comp_eq, preimage_id_eq, id_eq]

theorem contDiffWithinAtProp_self {f : E → E'} {s : Set E} {x : E} :
    ContDiffWithinAtProp 𝓘(𝕜, E) 𝓘(𝕜, E') n f s x ↔ ContDiffWithinAt 𝕜 n f s x :=
  contDiffWithinAtProp_self_source

theorem contDiffWithinAt_localInvariantProp_of_le (n m : WithTop ℕ∞) (hmn : m ≤ n) :
    (contDiffGroupoid n I).LocalInvariantProp (contDiffGroupoid n I')
      (ContDiffWithinAtProp I I' m) where
  is_local {s x u f} u_open xu := by
    have : I.symm ⁻¹' (s ∩ u) ∩ range I = I.symm ⁻¹' s ∩ range I ∩ I.symm ⁻¹' u := by
      simp only [inter_right_comm, preimage_inter]
    rw [ContDiffWithinAtProp, ContDiffWithinAtProp, this]
    symm
    apply contDiffWithinAt_inter
    have : u ∈ 𝓝 (I.symm (I x)) := by
      rw [ModelWithCorners.left_inv]
      exact u_open.mem_nhds xu
    apply ContinuousAt.preimage_mem_nhds I.continuous_symm.continuousAt this
  right_invariance' {s x f e} he hx h := by
    rw [ContDiffWithinAtProp] at h ⊢
    have : I x = (I ∘ e.symm ∘ I.symm) (I (e x)) := by simp only [hx, mfld_simps]
    rw [this] at h
    have : I (e x) ∈ I.symm ⁻¹' e.target ∩ range I := by simp only [hx, mfld_simps]
    have := (mem_groupoid_of_pregroupoid.2 he).2.contDiffWithinAt this
    convert (h.comp_inter _ (this.of_le hmn)).mono_of_mem_nhdsWithin _
      using 1
    · ext y; simp only [mfld_simps]
    refine mem_nhdsWithin.mpr
      ⟨I.symm ⁻¹' e.target, e.open_target.preimage I.continuous_symm, by
        simp_rw [mem_preimage, I.left_inv, e.mapsTo hx], ?_⟩
    mfld_set_tac
  congr_of_forall {s x f g} h hx hf := by
    apply hf.congr
    · intro y hy
      simp only [mfld_simps] at hy
      simp only [h, hy, mfld_simps]
    · simp only [hx, mfld_simps]
  left_invariance' {s x f e'} he' hs hx h := by
    rw [ContDiffWithinAtProp] at h ⊢
    have A : (I' ∘ f ∘ I.symm) (I x) ∈ I'.symm ⁻¹' e'.source ∩ range I' := by
      simp only [hx, mfld_simps]
    have := (mem_groupoid_of_pregroupoid.2 he').1.contDiffWithinAt A
    convert (this.of_le hmn).comp _ h _
    · ext y; simp only [mfld_simps]
    · intro y hy; simp only [mfld_simps] at hy; simpa only [hy, mfld_simps] using hs hy.1

theorem contDiffWithinAt_localInvariantProp (n : WithTop ℕ∞) :
    (contDiffGroupoid n I).LocalInvariantProp (contDiffGroupoid n I')
      (ContDiffWithinAtProp I I' n) :=
  contDiffWithinAt_localInvariantProp_of_le n n le_rfl

theorem contDiffWithinAtProp_mono_of_mem_nhdsWithin
    (n : WithTop ℕ∞) ⦃s x t⦄ ⦃f : H → H'⦄ (hts : s ∈ 𝓝[t] x)
    (h : ContDiffWithinAtProp I I' n f s x) : ContDiffWithinAtProp I I' n f t x := by
  refine h.mono_of_mem_nhdsWithin ?_
  refine inter_mem ?_ (mem_of_superset self_mem_nhdsWithin inter_subset_right)
  rwa [← Filter.mem_map, ← I.image_eq, I.symm_map_nhdsWithin_image]

theorem contDiffWithinAtProp_id (x : H) : ContDiffWithinAtProp I I n id univ x := by
  simp only [ContDiffWithinAtProp, id_comp, preimage_univ, univ_inter]
  have : ContDiffWithinAt 𝕜 n id (range I) (I x) := contDiff_id.contDiffAt.contDiffWithinAt
  refine this.congr (fun y hy => ?_) ?_
  · simp only [ModelWithCorners.right_inv I hy, mfld_simps]
  · simp only [mfld_simps]

variable (I I') in

def ContMDiffWithinAt (n : WithTop ℕ∞) (f : M → M') (s : Set M) (x : M) :=
  LiftPropWithinAt (ContDiffWithinAtProp I I' n) f s x

variable (I I') in

def ContMDiffAt (n : WithTop ℕ∞) (f : M → M') (x : M) :=
  ContMDiffWithinAt I I' n f univ x

theorem contMDiffAt_iff {n : WithTop ℕ∞} {f : M → M'} {x : M} :
    ContMDiffAt I I' n f x ↔
      ContinuousAt f x ∧
        ContDiffWithinAt 𝕜 n (extChartAt I' (f x) ∘ f ∘ (extChartAt I x).symm) (range I)
          (extChartAt I x x) :=
  liftPropAt_iff.trans <| by rw [ContDiffWithinAtProp, preimage_univ, univ_inter]; rfl

variable (I I') in

def ContMDiffOn (n : WithTop ℕ∞) (f : M → M') (s : Set M) :=
  ∀ x ∈ s, ContMDiffWithinAt I I' n f s x

variable (I I') in

def ContMDiff (n : WithTop ℕ∞) (f : M → M') :=
  ∀ x, ContMDiffAt I I' n f x

/-! ### Deducing smoothness from higher smoothness -/

theorem ContMDiffWithinAt.of_le (hf : ContMDiffWithinAt I I' n f s x) (le : m ≤ n) :
    ContMDiffWithinAt I I' m f s x := by
  simp only [ContMDiffWithinAt] at hf ⊢
  exact ⟨hf.1, hf.2.of_le (mod_cast le)⟩

theorem ContMDiffAt.of_le (hf : ContMDiffAt I I' n f x) (le : m ≤ n) : ContMDiffAt I I' m f x :=
  ContMDiffWithinAt.of_le hf le

theorem ContMDiffOn.of_le (hf : ContMDiffOn I I' n f s) (le : m ≤ n) : ContMDiffOn I I' m f s :=
  fun x hx => (hf x hx).of_le le

theorem ContMDiff.of_le (hf : ContMDiff I I' n f) (le : m ≤ n) : ContMDiff I I' m f := fun x =>
  (hf x).of_le le

/-! ### Basic properties of `C^n` functions between manifolds -/
