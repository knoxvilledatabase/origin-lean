/-
Extracted from Topology/PartitionOfUnity.lean
Genuine: 64 | Conflates: 0 | Dissolved: 0 | Infrastructure: 7
-/
import Origin.Core
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.ShrinkingLemma
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.ContinuousMap.Ordered

noncomputable section

/-!
# Continuous partition of unity

In this file we define `PartitionOfUnity (ι X : Type*) [TopologicalSpace X] (s : Set X := univ)`
to be a continuous partition of unity on `s` indexed by `ι`. More precisely,
`f : PartitionOfUnity ι X s` is a collection of continuous functions `f i : C(X, ℝ)`, `i : ι`,
such that

* the supports of `f i` form a locally finite family of sets;
* each `f i` is nonnegative;
* `∑ᶠ i, f i x = 1` for all `x ∈ s`;
* `∑ᶠ i, f i x ≤ 1` for all `x : X`.

In the case `s = univ` the last assumption follows from the previous one but it is convenient to
have this assumption in the case `s ≠ univ`.

We also define a bump function covering,
`BumpCovering (ι X : Type*) [TopologicalSpace X] (s : Set X := univ)`, to be a collection of
functions `f i : C(X, ℝ)`, `i : ι`, such that

* the supports of `f i` form a locally finite family of sets;
* each `f i` is nonnegative;
* for each `x ∈ s` there exists `i : ι` such that `f i y = 1` in a neighborhood of `x`.

The term is motivated by the smooth case.

If `f` is a bump function covering indexed by a linearly ordered type, then
`g i x = f i x * ∏ᶠ j < i, (1 - f j x)` is a partition of unity, see
`BumpCovering.toPartitionOfUnity`. Note that only finitely many terms `1 - f j x` are not equal
to one, so this product is well-defined.

Note that `g i x = ∏ᶠ j ≤ i, (1 - f j x) - ∏ᶠ j < i, (1 - f j x)`, so most terms in the sum
`∑ᶠ i, g i x` cancel, and we get `∑ᶠ i, g i x = 1 - ∏ᶠ i, (1 - f i x)`, and the latter product
equals zero because one of `f i x` is equal to one.

We say that a partition of unity or a bump function covering `f` is *subordinate* to a family of
sets `U i`, `i : ι`, if the closure of the support of each `f i` is included in `U i`. We use
Urysohn's Lemma to prove that a locally finite open covering of a normal topological space admits a
subordinate bump function covering (hence, a subordinate partition of unity), see
`BumpCovering.exists_isSubordinate_of_locallyFinite`. If `X` is a paracompact space, then any
open covering admits a locally finite refinement, hence it admits a subordinate bump function
covering and a subordinate partition of unity, see `BumpCovering.exists_isSubordinate`.

We also provide two slightly more general versions of these lemmas,
`BumpCovering.exists_isSubordinate_of_locallyFinite_of_prop` and
`BumpCovering.exists_isSubordinate_of_prop`, to be used later in the construction of a smooth
partition of unity.

## Implementation notes

Most (if not all) books only define a partition of unity of the whole space. However, quite a few
proofs only deal with `f i` such that `tsupport (f i)` meets a specific closed subset, and
it is easier to formalize these proofs if we don't have other functions right away.

We use `WellOrderingRel j i` instead of `j < i` in the definition of
`BumpCovering.toPartitionOfUnity` to avoid a `[LinearOrder ι]` assumption. While
`WellOrderingRel j i` is a well order, not only a strict linear order, we never use this property.

## Tags

partition of unity, bump function, Urysohn's lemma, normal space, paracompact space
-/

universe u v

open Function Set Filter Topology

noncomputable section

structure PartitionOfUnity (ι X : Type*) [TopologicalSpace X] (s : Set X := univ) where
  /-- The collection of continuous functions underlying this partition of unity -/
  toFun : ι → C(X, ℝ)
  /-- the supports of the underlying functions are a locally finite family of sets -/
  locallyFinite' : LocallyFinite fun i => support (toFun i)
  /-- the functions are non-negative -/
  nonneg' : 0 ≤ toFun
  /-- the functions sum up to one on `s` -/
  sum_eq_one' : ∀ x ∈ s, ∑ᶠ i, toFun i x = 1
  /-- the functions sum up to at most one, globally -/
  sum_le_one' : ∀ x, ∑ᶠ i, toFun i x ≤ 1

structure BumpCovering (ι X : Type*) [TopologicalSpace X] (s : Set X := univ) where
  /-- The collections of continuous functions underlying this bump covering -/
  toFun : ι → C(X, ℝ)
  /-- the supports of the underlying functions are a locally finite family of sets -/
  locallyFinite' : LocallyFinite fun i => support (toFun i)
  /-- the functions are non-negative -/
  nonneg' : 0 ≤ toFun
  /-- the functions are each at most one -/
  le_one' : toFun ≤ 1
  /-- Each point `x ∈ s` belongs to the interior of `{x | f i x = 1}` for some `i`. -/
  eventuallyEq_one' : ∀ x ∈ s, ∃ i, toFun i =ᶠ[𝓝 x] 1

variable {ι : Type u} {X : Type v} [TopologicalSpace X]

namespace PartitionOfUnity

variable {E : Type*} [AddCommMonoid E] [SMulWithZero ℝ E] [TopologicalSpace E] [ContinuousSMul ℝ E]
  {s : Set X} (f : PartitionOfUnity ι X s)

instance : FunLike (PartitionOfUnity ι X s) ι C(X, ℝ) where
  coe := toFun
  coe_injective' f g h := by cases f; cases g; congr

protected theorem locallyFinite : LocallyFinite fun i => support (f i) :=
  f.locallyFinite'

theorem locallyFinite_tsupport : LocallyFinite fun i => tsupport (f i) :=
  f.locallyFinite.closure

theorem nonneg (i : ι) (x : X) : 0 ≤ f i x :=
  f.nonneg' i x

theorem sum_eq_one {x : X} (hx : x ∈ s) : ∑ᶠ i, f i x = 1 :=
  f.sum_eq_one' x hx

theorem exists_pos {x : X} (hx : x ∈ s) : ∃ i, 0 < f i x := by
  have H := f.sum_eq_one hx
  contrapose! H
  simpa only [fun i => (H i).antisymm (f.nonneg i x), finsum_zero] using zero_ne_one

theorem sum_le_one (x : X) : ∑ᶠ i, f i x ≤ 1 :=
  f.sum_le_one' x

theorem sum_nonneg (x : X) : 0 ≤ ∑ᶠ i, f i x :=
  finsum_nonneg fun i => f.nonneg i x

theorem le_one (i : ι) (x : X) : f i x ≤ 1 :=
  (single_le_finsum i (f.locallyFinite.point_finite x) fun j => f.nonneg j x).trans (f.sum_le_one x)

section finsupport

variable {s : Set X} (ρ : PartitionOfUnity ι X s) (x₀ : X)

def finsupport : Finset ι := (ρ.locallyFinite.point_finite x₀).toFinset

@[simp]
theorem mem_finsupport (x₀ : X) {i} :
    i ∈ ρ.finsupport x₀ ↔ i ∈ support fun i ↦ ρ i x₀ := by
  simp only [finsupport, mem_support, Finite.mem_toFinset, mem_setOf_eq]

@[simp]
theorem coe_finsupport (x₀ : X) :
    (ρ.finsupport x₀ : Set ι) = support fun i ↦ ρ i x₀ := by
  ext
  rw [Finset.mem_coe, mem_finsupport]

variable {x₀ : X}

theorem sum_finsupport (hx₀ : x₀ ∈ s) : ∑ i ∈ ρ.finsupport x₀, ρ i x₀ = 1 := by
  rw [← ρ.sum_eq_one hx₀, finsum_eq_sum_of_support_subset _ (ρ.coe_finsupport x₀).superset]

theorem sum_finsupport' (hx₀ : x₀ ∈ s) {I : Finset ι} (hI : ρ.finsupport x₀ ⊆ I) :
    ∑ i ∈ I, ρ i x₀ = 1 := by
  classical
  rw [← Finset.sum_sdiff hI, ρ.sum_finsupport hx₀]
  suffices ∑ i ∈ I \ ρ.finsupport x₀, (ρ i) x₀ = ∑ i ∈ I \ ρ.finsupport x₀, 0 by
    rw [this, add_left_eq_self, Finset.sum_const_zero]
  apply Finset.sum_congr rfl
  rintro x hx
  simp only [Finset.mem_sdiff, ρ.mem_finsupport, mem_support, Classical.not_not] at hx
  exact hx.2

theorem sum_finsupport_smul_eq_finsum {M : Type*} [AddCommGroup M] [Module ℝ M] (φ : ι → X → M) :
    ∑ i ∈ ρ.finsupport x₀, ρ i x₀ • φ i x₀ = ∑ᶠ i, ρ i x₀ • φ i x₀ := by
  apply (finsum_eq_sum_of_support_subset _ _).symm
  have : (fun i ↦ (ρ i) x₀ • φ i x₀) = (fun i ↦ (ρ i) x₀) • (fun i ↦ φ i x₀) :=
    funext fun _ => (Pi.smul_apply' _ _ _).symm
  rw [ρ.coe_finsupport x₀, this, support_smul]
  exact inter_subset_left

end finsupport

section fintsupport -- partitions of unity have locally finite `tsupport`

variable {s : Set X} (ρ : PartitionOfUnity ι X s) (x₀ : X)

theorem finite_tsupport : {i | x₀ ∈ tsupport (ρ i)}.Finite := by
  rcases ρ.locallyFinite x₀ with ⟨t, t_in, ht⟩
  apply ht.subset
  rintro i hi
  simp only [inter_comm]
  exact mem_closure_iff_nhds.mp hi t t_in

def fintsupport (x₀ : X) : Finset ι :=
  (ρ.finite_tsupport x₀).toFinset

theorem mem_fintsupport_iff (i : ι) : i ∈ ρ.fintsupport x₀ ↔ x₀ ∈ tsupport (ρ i) :=
  Finite.mem_toFinset _

theorem eventually_fintsupport_subset :
    ∀ᶠ y in 𝓝 x₀, ρ.fintsupport y ⊆ ρ.fintsupport x₀ := by
  apply (ρ.locallyFinite.closure.eventually_subset (fun _ ↦ isClosed_closure) x₀).mono
  intro y hy z hz
  rw [PartitionOfUnity.mem_fintsupport_iff] at *
  exact hy hz

theorem finsupport_subset_fintsupport : ρ.finsupport x₀ ⊆ ρ.fintsupport x₀ := fun i hi ↦ by
  rw [ρ.mem_fintsupport_iff]
  apply subset_closure
  exact (ρ.mem_finsupport x₀).mp hi

theorem eventually_finsupport_subset : ∀ᶠ y in 𝓝 x₀, ρ.finsupport y ⊆ ρ.fintsupport x₀ :=
  (ρ.eventually_fintsupport_subset x₀).mono
    fun y hy ↦ (ρ.finsupport_subset_fintsupport y).trans hy

end fintsupport

theorem continuous_smul {g : X → E} {i : ι} (hg : ∀ x ∈ tsupport (f i), ContinuousAt g x) :
    Continuous fun x => f i x • g x :=
  continuous_of_tsupport fun x hx =>
    ((f i).continuousAt x).smul <| hg x <| tsupport_smul_subset_left _ _ hx

theorem continuous_finsum_smul [ContinuousAdd E] {g : ι → X → E}
    (hg : ∀ (i), ∀ x ∈ tsupport (f i), ContinuousAt (g i) x) :
    Continuous fun x => ∑ᶠ i, f i x • g i x :=
  (continuous_finsum fun i => f.continuous_smul (hg i)) <|
    f.locallyFinite.subset fun _ => support_smul_subset_left _ _

def IsSubordinate (U : ι → Set X) : Prop :=
  ∀ i, tsupport (f i) ⊆ U i

variable {f}

theorem exists_finset_nhd' {s : Set X} (ρ : PartitionOfUnity ι X s) (x₀ : X) :
    ∃ I : Finset ι, (∀ᶠ x in 𝓝[s] x₀, ∑ i ∈ I, ρ i x = 1) ∧
      ∀ᶠ x in 𝓝 x₀, support (ρ · x) ⊆ I := by
  rcases ρ.locallyFinite.exists_finset_support x₀ with ⟨I, hI⟩
  refine ⟨I, eventually_nhdsWithin_iff.mpr (hI.mono fun x hx x_in ↦ ?_), hI⟩
  have : ∑ᶠ i : ι, ρ i x = ∑ i ∈ I, ρ i x := finsum_eq_sum_of_support_subset _ hx
  rwa [eq_comm, ρ.sum_eq_one x_in] at this

theorem exists_finset_nhd (ρ : PartitionOfUnity ι X univ) (x₀ : X) :
    ∃ I : Finset ι, ∀ᶠ x in 𝓝 x₀, ∑ i ∈ I, ρ i x = 1 ∧ support (ρ · x) ⊆ I := by
  rcases ρ.exists_finset_nhd' x₀ with ⟨I, H⟩
  use I
  rwa [nhdsWithin_univ, ← eventually_and] at H

theorem exists_finset_nhd_support_subset {U : ι → Set X} (hso : f.IsSubordinate U)
    (ho : ∀ i, IsOpen (U i)) (x : X) :
    ∃ is : Finset ι, ∃ n ∈ 𝓝 x, n ⊆ ⋂ i ∈ is, U i ∧ ∀ z ∈ n, (support (f · z)) ⊆ is :=
  f.locallyFinite.exists_finset_nhd_support_subset hso ho x

theorem IsSubordinate.continuous_finsum_smul [ContinuousAdd E] {U : ι → Set X}
    (ho : ∀ i, IsOpen (U i)) (hf : f.IsSubordinate U) {g : ι → X → E}
    (hg : ∀ i, ContinuousOn (g i) (U i)) : Continuous fun x => ∑ᶠ i, f i x • g i x :=
  f.continuous_finsum_smul fun i _ hx => (hg i).continuousAt <| (ho i).mem_nhds <| hf i hx

end PartitionOfUnity

namespace BumpCovering

variable {s : Set X} (f : BumpCovering ι X s)

instance : FunLike (BumpCovering ι X s) ι C(X, ℝ) where
  coe := toFun
  coe_injective' f g h := by cases f; cases g; congr

protected theorem locallyFinite : LocallyFinite fun i => support (f i) :=
  f.locallyFinite'

theorem locallyFinite_tsupport : LocallyFinite fun i => tsupport (f i) :=
  f.locallyFinite.closure

protected theorem point_finite (x : X) : { i | f i x ≠ 0 }.Finite :=
  f.locallyFinite.point_finite x

theorem nonneg (i : ι) (x : X) : 0 ≤ f i x :=
  f.nonneg' i x

theorem le_one (i : ι) (x : X) : f i x ≤ 1 :=
  f.le_one' i x

open Classical in

protected def single (i : ι) (s : Set X) : BumpCovering ι X s where
  toFun := Pi.single i 1
  locallyFinite' x := by
    refine ⟨univ, univ_mem, (finite_singleton i).subset ?_⟩
    rintro j ⟨x, hx, -⟩
    contrapose! hx
    rw [mem_singleton_iff] at hx
    simp [hx]
  nonneg' := le_update_iff.2 ⟨fun _ => zero_le_one, fun _ _ => le_rfl⟩
  le_one' := update_le_iff.2 ⟨le_rfl, fun _ _ _ => zero_le_one⟩
  eventuallyEq_one' x _ := ⟨i, by rw [Pi.single_eq_same, ContinuousMap.coe_one]⟩

open Classical in

instance [Inhabited ι] : Inhabited (BumpCovering ι X s) :=
  ⟨BumpCovering.single default s⟩

def IsSubordinate (f : BumpCovering ι X s) (U : ι → Set X) : Prop :=
  ∀ i, tsupport (f i) ⊆ U i

theorem IsSubordinate.mono {f : BumpCovering ι X s} {U V : ι → Set X} (hU : f.IsSubordinate U)
    (hV : ∀ i, U i ⊆ V i) : f.IsSubordinate V :=
  fun i => Subset.trans (hU i) (hV i)

theorem exists_isSubordinate_of_locallyFinite_of_prop [NormalSpace X] (p : (X → ℝ) → Prop)
    (h01 : ∀ s t, IsClosed s → IsClosed t → Disjoint s t →
      ∃ f : C(X, ℝ), p f ∧ EqOn f 0 s ∧ EqOn f 1 t ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1)
    (hs : IsClosed s) (U : ι → Set X) (ho : ∀ i, IsOpen (U i)) (hf : LocallyFinite U)
    (hU : s ⊆ ⋃ i, U i) : ∃ f : BumpCovering ι X s, (∀ i, p (f i)) ∧ f.IsSubordinate U := by
  rcases exists_subset_iUnion_closure_subset hs ho (fun x _ => hf.point_finite x) hU with
    ⟨V, hsV, hVo, hVU⟩
  have hVU' : ∀ i, V i ⊆ U i := fun i => Subset.trans subset_closure (hVU i)
  rcases exists_subset_iUnion_closure_subset hs hVo (fun x _ => (hf.subset hVU').point_finite x)
      hsV with
    ⟨W, hsW, hWo, hWV⟩
  choose f hfp hf0 hf1 hf01 using fun i =>
    h01 _ _ (isClosed_compl_iff.2 <| hVo i) isClosed_closure
      (disjoint_right.2 fun x hx => Classical.not_not.2 (hWV i hx))
  have hsupp : ∀ i, support (f i) ⊆ V i := fun i => support_subset_iff'.2 (hf0 i)
  refine ⟨⟨f, hf.subset fun i => Subset.trans (hsupp i) (hVU' i), fun i x => (hf01 i x).1,
      fun i x => (hf01 i x).2, fun x hx => ?_⟩,
    hfp, fun i => Subset.trans (closure_mono (hsupp i)) (hVU i)⟩
  rcases mem_iUnion.1 (hsW hx) with ⟨i, hi⟩
  exact ⟨i, ((hf1 i).mono subset_closure).eventuallyEq_of_mem ((hWo i).mem_nhds hi)⟩

theorem exists_isSubordinate_of_locallyFinite [NormalSpace X] (hs : IsClosed s) (U : ι → Set X)
    (ho : ∀ i, IsOpen (U i)) (hf : LocallyFinite U) (hU : s ⊆ ⋃ i, U i) :
    ∃ f : BumpCovering ι X s, f.IsSubordinate U :=
  let ⟨f, _, hfU⟩ :=
    exists_isSubordinate_of_locallyFinite_of_prop (fun _ => True)
      (fun _ _ hs ht hd =>
        (exists_continuous_zero_one_of_isClosed hs ht hd).imp fun _ hf => ⟨trivial, hf⟩)
      hs U ho hf hU
  ⟨f, hfU⟩

theorem exists_isSubordinate_of_prop [NormalSpace X] [ParacompactSpace X] (p : (X → ℝ) → Prop)
    (h01 : ∀ s t, IsClosed s → IsClosed t → Disjoint s t →
      ∃ f : C(X, ℝ), p f ∧ EqOn f 0 s ∧ EqOn f 1 t ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1)
    (hs : IsClosed s) (U : ι → Set X) (ho : ∀ i, IsOpen (U i)) (hU : s ⊆ ⋃ i, U i) :
    ∃ f : BumpCovering ι X s, (∀ i, p (f i)) ∧ f.IsSubordinate U := by
  rcases precise_refinement_set hs _ ho hU with ⟨V, hVo, hsV, hVf, hVU⟩
  rcases exists_isSubordinate_of_locallyFinite_of_prop p h01 hs V hVo hVf hsV with ⟨f, hfp, hf⟩
  exact ⟨f, hfp, hf.mono hVU⟩

theorem exists_isSubordinate [NormalSpace X] [ParacompactSpace X] (hs : IsClosed s) (U : ι → Set X)
    (ho : ∀ i, IsOpen (U i)) (hU : s ⊆ ⋃ i, U i) : ∃ f : BumpCovering ι X s, f.IsSubordinate U := by
  rcases precise_refinement_set hs _ ho hU with ⟨V, hVo, hsV, hVf, hVU⟩
  rcases exists_isSubordinate_of_locallyFinite hs V hVo hVf hsV with ⟨f, hf⟩
  exact ⟨f, hf.mono hVU⟩

theorem exists_isSubordinate_of_locallyFinite_of_prop_t2space [LocallyCompactSpace X] [T2Space X]
    (p : (X → ℝ) → Prop) (h01 : ∀ s t, IsClosed s → IsCompact t → Disjoint s t → ∃ f : C(X, ℝ),
    p f ∧ EqOn f 0 s ∧ EqOn f 1 t ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1)
    (hs : IsCompact s) (U : ι → Set X) (ho : ∀ i, IsOpen (U i)) (hf : LocallyFinite U)
    (hU : s ⊆ ⋃ i, U i) :
    ∃ f : BumpCovering ι X s, (∀ i, p (f i)) ∧ f.IsSubordinate U ∧
      ∀ i, HasCompactSupport (f i) := by
  rcases exists_subset_iUnion_closure_subset_t2space hs ho (fun x _ => hf.point_finite x) hU with
    ⟨V, hsV, hVo, hVU, hcp⟩
  have hVU' i : V i ⊆ U i := subset_closure.trans (hVU i)
  rcases exists_subset_iUnion_closure_subset_t2space hs hVo
    (fun x _ => (hf.subset hVU').point_finite x) hsV with ⟨W, hsW, hWo, hWV, hWc⟩
  choose f hfp hf0 hf1 hf01 using fun i =>
    h01 _ _ (isClosed_compl_iff.2 <| hVo i) (hWc i)
      (disjoint_right.2 fun x hx => Classical.not_not.2 (hWV i hx))
  have hsupp i : support (f i) ⊆ V i := support_subset_iff'.2 (hf0 i)
  refine ⟨⟨f, hf.subset fun i => Subset.trans (hsupp i) (hVU' i), fun i x => (hf01 i x).1,
      fun i x => (hf01 i x).2, fun x hx => ?_⟩,
    hfp, fun i => Subset.trans (closure_mono (hsupp i)) (hVU i),
    fun i => IsCompact.of_isClosed_subset (hcp i) isClosed_closure <| closure_mono (hsupp i)⟩
  rcases mem_iUnion.1 (hsW hx) with ⟨i, hi⟩
  exact ⟨i, ((hf1 i).mono subset_closure).eventuallyEq_of_mem ((hWo i).mem_nhds hi)⟩

theorem exists_isSubordinate_hasCompactSupport_of_locallyFinite_t2space [LocallyCompactSpace X]
    [T2Space X]
    (hs : IsCompact s) (U : ι → Set X) (ho : ∀ i, IsOpen (U i)) (hf : LocallyFinite U)
    (hU : s ⊆ ⋃ i, U i) :
    ∃ f : BumpCovering ι X s, f.IsSubordinate U ∧ ∀ i, HasCompactSupport (f i) := by
  -- need to switch 0 and 1 in `exists_continuous_zero_one_of_isCompact`
  simpa using
    exists_isSubordinate_of_locallyFinite_of_prop_t2space (fun _ => True)
      (fun _ _ ht hs hd =>
        (exists_continuous_zero_one_of_isCompact' hs ht hd.symm).imp fun _ hf => ⟨trivial, hf⟩)
      hs U ho hf hU

def ind (x : X) (hx : x ∈ s) : ι :=
  (f.eventuallyEq_one' x hx).choose

theorem eventuallyEq_one (x : X) (hx : x ∈ s) : f (f.ind x hx) =ᶠ[𝓝 x] 1 :=
  (f.eventuallyEq_one' x hx).choose_spec

theorem ind_apply (x : X) (hx : x ∈ s) : f (f.ind x hx) x = 1 :=
  (f.eventuallyEq_one x hx).eq_of_nhds

def toPOUFun (i : ι) (x : X) : ℝ :=
  f i x * ∏ᶠ (j) (_ : WellOrderingRel j i), (1 - f j x)

theorem toPOUFun_zero_of_zero {i : ι} {x : X} (h : f i x = 0) : f.toPOUFun i x = 0 := by
  rw [toPOUFun, h, zero_mul]

theorem support_toPOUFun_subset (i : ι) : support (f.toPOUFun i) ⊆ support (f i) :=
  fun _ => mt <| f.toPOUFun_zero_of_zero

open Classical in

theorem toPOUFun_eq_mul_prod (i : ι) (x : X) (t : Finset ι)
    (ht : ∀ j, WellOrderingRel j i → f j x ≠ 0 → j ∈ t) :
    f.toPOUFun i x = f i x * ∏ j ∈ t.filter fun j => WellOrderingRel j i, (1 - f j x) := by
  refine congr_arg _ (finprod_cond_eq_prod_of_cond_iff _ fun {j} hj => ?_)
  rw [Ne, sub_eq_self] at hj
  rw [Finset.mem_filter, Iff.comm, and_iff_right_iff_imp]
  exact flip (ht j) hj

theorem sum_toPOUFun_eq (x : X) : ∑ᶠ i, f.toPOUFun i x = 1 - ∏ᶠ i, (1 - f i x) := by
  set s := (f.point_finite x).toFinset
  have hs : (s : Set ι) = { i | f i x ≠ 0 } := Finite.coe_toFinset _
  have A : (support fun i => toPOUFun f i x) ⊆ s := by
    rw [hs]
    exact fun i hi => f.support_toPOUFun_subset i hi
  have B : (mulSupport fun i => 1 - f i x) ⊆ s := by
    rw [hs, mulSupport_one_sub]
    exact fun i => id
  classical
  letI : LinearOrder ι := linearOrderOfSTO WellOrderingRel
  rw [finsum_eq_sum_of_support_subset _ A, finprod_eq_prod_of_mulSupport_subset _ B,
    Finset.prod_one_sub_ordered, sub_sub_cancel]
  refine Finset.sum_congr rfl fun i _ => ?_
  convert f.toPOUFun_eq_mul_prod _ _ _ fun j _ hj => _
  rwa [Finite.mem_toFinset]

open Classical in

theorem exists_finset_toPOUFun_eventuallyEq (i : ι) (x : X) : ∃ t : Finset ι,
    f.toPOUFun i =ᶠ[𝓝 x] f i * ∏ j ∈ t.filter fun j => WellOrderingRel j i, (1 - f j) := by
  rcases f.locallyFinite x with ⟨U, hU, hf⟩
  use hf.toFinset
  filter_upwards [hU] with y hyU
  simp only [ContinuousMap.coe_prod, Pi.mul_apply, Finset.prod_apply]
  apply toPOUFun_eq_mul_prod
  intro j _ hj
  exact hf.mem_toFinset.2 ⟨y, ⟨hj, hyU⟩⟩

theorem continuous_toPOUFun (i : ι) : Continuous (f.toPOUFun i) := by
  refine (f i).continuous.mul <|
    continuous_finprod_cond (fun j _ => continuous_const.sub (f j).continuous) ?_
  simp only [mulSupport_one_sub]
  exact f.locallyFinite

def toPartitionOfUnity : PartitionOfUnity ι X s where
  toFun i := ⟨f.toPOUFun i, f.continuous_toPOUFun i⟩
  locallyFinite' := f.locallyFinite.subset f.support_toPOUFun_subset
  nonneg' i x :=
    mul_nonneg (f.nonneg i x) (finprod_cond_nonneg fun j _ => sub_nonneg.2 <| f.le_one j x)
  sum_eq_one' x hx := by
    simp only [ContinuousMap.coe_mk, sum_toPOUFun_eq, sub_eq_self]
    apply finprod_eq_zero (fun i => 1 - f i x) (f.ind x hx)
    · simp only [f.ind_apply x hx, sub_self]
    · rw [mulSupport_one_sub]
      exact f.point_finite x
  sum_le_one' x := by
    simp only [ContinuousMap.coe_mk, sum_toPOUFun_eq, sub_le_self_iff]
    exact finprod_nonneg fun i => sub_nonneg.2 <| f.le_one i x

open Classical in

theorem toPartitionOfUnity_eq_mul_prod (i : ι) (x : X) (t : Finset ι)
    (ht : ∀ j, WellOrderingRel j i → f j x ≠ 0 → j ∈ t) :
    f.toPartitionOfUnity i x = f i x * ∏ j ∈ t.filter fun j => WellOrderingRel j i, (1 - f j x) :=
  f.toPOUFun_eq_mul_prod i x t ht

open Classical in

theorem exists_finset_toPartitionOfUnity_eventuallyEq (i : ι) (x : X) : ∃ t : Finset ι,
    f.toPartitionOfUnity i =ᶠ[𝓝 x] f i * ∏ j ∈ t.filter fun j => WellOrderingRel j i, (1 - f j) :=
  f.exists_finset_toPOUFun_eventuallyEq i x

theorem toPartitionOfUnity_zero_of_zero {i : ι} {x : X} (h : f i x = 0) :
    f.toPartitionOfUnity i x = 0 :=
  f.toPOUFun_zero_of_zero h

theorem support_toPartitionOfUnity_subset (i : ι) :
    support (f.toPartitionOfUnity i) ⊆ support (f i) :=
  f.support_toPOUFun_subset i

theorem sum_toPartitionOfUnity_eq (x : X) :
    ∑ᶠ i, f.toPartitionOfUnity i x = 1 - ∏ᶠ i, (1 - f i x) :=
  f.sum_toPOUFun_eq x

theorem IsSubordinate.toPartitionOfUnity {f : BumpCovering ι X s} {U : ι → Set X}
    (h : f.IsSubordinate U) : f.toPartitionOfUnity.IsSubordinate U :=
  fun i => Subset.trans (closure_mono <| f.support_toPartitionOfUnity_subset i) (h i)

end BumpCovering

namespace PartitionOfUnity

variable {s : Set X}

instance [Inhabited ι] : Inhabited (PartitionOfUnity ι X s) :=
  ⟨BumpCovering.toPartitionOfUnity default⟩

theorem exists_isSubordinate_of_locallyFinite [NormalSpace X] (hs : IsClosed s) (U : ι → Set X)
    (ho : ∀ i, IsOpen (U i)) (hf : LocallyFinite U) (hU : s ⊆ ⋃ i, U i) :
    ∃ f : PartitionOfUnity ι X s, f.IsSubordinate U :=
  let ⟨f, hf⟩ := BumpCovering.exists_isSubordinate_of_locallyFinite hs U ho hf hU
  ⟨f.toPartitionOfUnity, hf.toPartitionOfUnity⟩

theorem exists_isSubordinate [NormalSpace X] [ParacompactSpace X] (hs : IsClosed s) (U : ι → Set X)
    (ho : ∀ i, IsOpen (U i)) (hU : s ⊆ ⋃ i, U i) :
    ∃ f : PartitionOfUnity ι X s, f.IsSubordinate U :=
  let ⟨f, hf⟩ := BumpCovering.exists_isSubordinate hs U ho hU
  ⟨f.toPartitionOfUnity, hf.toPartitionOfUnity⟩

theorem exists_isSubordinate_of_locallyFinite_t2space [LocallyCompactSpace X] [T2Space X]
    (hs : IsCompact s) (U : ι → Set X) (ho : ∀ i, IsOpen (U i)) (hf : LocallyFinite U)
    (hU : s ⊆ ⋃ i, U i) :
    ∃ f : PartitionOfUnity ι X s, f.IsSubordinate U ∧ ∀ i, HasCompactSupport (f i) :=
  let ⟨f, hfsub, hfcp⟩ :=
    BumpCovering.exists_isSubordinate_hasCompactSupport_of_locallyFinite_t2space hs U ho hf hU
  ⟨f.toPartitionOfUnity, hfsub.toPartitionOfUnity, fun i => IsCompact.of_isClosed_subset (hfcp i)
    isClosed_closure <| closure_mono (f.support_toPartitionOfUnity_subset i)⟩

end PartitionOfUnity

theorem exists_continuous_sum_one_of_isOpen_isCompact [T2Space X] [LocallyCompactSpace X]
    {n : ℕ} {t : Set X} {s : Fin n → Set X} (hs : ∀ (i : Fin n), IsOpen (s i)) (htcp : IsCompact t)
    (hst : t ⊆ ⋃ i, s i) :
    ∃ f : Fin n → C(X, ℝ), (∀ (i : Fin n), tsupport (f i) ⊆ s i) ∧ EqOn (∑ i, f i) 1 t
      ∧ (∀ (i : Fin n), ∀ (x : X), f i x ∈ Icc (0 : ℝ) 1)
      ∧ (∀ (i : Fin n), HasCompactSupport (f i)) := by
  obtain ⟨f, hfsub, hfcp⟩ := PartitionOfUnity.exists_isSubordinate_of_locallyFinite_t2space htcp s
    hs (locallyFinite_of_finite _) hst
  use f
  refine ⟨fun i ↦ hfsub i, ?_, ?_, fun i => hfcp i⟩
  · intro x hx
    simp only [Finset.sum_apply, Pi.one_apply]
    have h := f.sum_eq_one' x hx
    simp at h
    rw [finsum_eq_sum (fun i => (f.toFun i) x)
      (Finite.subset finite_univ (subset_univ (support fun i ↦ (f.toFun i) x)))] at h
    simp only [Finite.toFinset_setOf, ne_eq] at h
    rw [← h, ← Finset.sum_subset
      (Finset.subset_univ (Finset.filter (fun (j : Fin n) ↦ ¬(f.toFun j) x = 0) Finset.univ))
      (by intro j hju hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Decidable.not_not] at hj
          exact hj)]
    rfl
  intro i x
  refine ⟨f.nonneg i x, ?_⟩
  by_cases h0 : f i x = 0
  · rw [h0]
    exact zero_le_one
  rw [← Finset.sum_singleton (f ·  x) i]
  apply le_trans _ (f.sum_le_one' x)
  rw [finsum_eq_sum (f.toFun ·  x) (by exact toFinite (support (f.toFun · x)))]
  simp only [Finite.toFinset_setOf, ne_eq]
  gcongr with z hz
  · exact fun j _ _ => f.nonneg j x
  simp only [Finset.singleton_subset_iff, Finset.mem_filter, Finset.mem_univ, true_and]
  exact h0
