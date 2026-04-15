/-
Extracted from Geometry/Manifold/VectorBundle/SmoothSection.lean
Genuine: 26 of 34 | Dissolved: 8 | Infrastructure: 0
-/
import Origin.Core

/-!
# `C^n` sections

In this file we define the type `ContMDiffSection` of `n` times continuously differentiable
sections of a vector bundle over a manifold `M` and prove that it's a module over the base field.

In passing, we prove that binary and finite sums, differences and scalar products of `C^n`
sections are `C^n`.

-/

open Bundle Filter Function

open scoped Bundle Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  -- `F` model fiber
  (n : WithTop ℕ∞)
  (V : M → Type*) [TopologicalSpace (TotalSpace F V)]
  -- `V` vector bundle
  [∀ x : M, TopologicalSpace (V x)] [FiberBundle F V]

section operations

variable [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [VectorBundle 𝕜 F V]

variable {I F n V}

variable {f : M → 𝕜} {a : 𝕜} {s t : Π x : M, V x} {u : Set M} {x₀ : M}

lemma ContMDiffWithinAt.add_section (hs : CMDiffAt[u] n (T% s) x₀) (ht : CMDiffAt[u] n (T% t) x₀) :
    CMDiffAt[u] n (T% (s + t)) x₀ := by
  rw [contMDiffWithinAt_section] at hs ht ⊢
  set e := trivializationAt F V x₀
  refine (hs.add ht).congr_of_eventuallyEq ?_ ?_
  · apply eventually_of_mem (U := e.baseSet)
    · exact mem_nhdsWithin_of_mem_nhds <|
        (e.open_baseSet.mem_nhds <| mem_baseSet_trivializationAt F V x₀)
    · intro x hx
      apply (e.linear 𝕜 hx).1
  · apply (e.linear 𝕜 (FiberBundle.mem_baseSet_trivializationAt' x₀)).1

lemma ContMDiffAt.add_section (hs : CMDiffAt n (T% s) x₀) (ht : CMDiffAt n (T% t) x₀) :
    CMDiffAt n (T% (s + t)) x₀ := by
  rw [← contMDiffWithinAt_univ] at hs ⊢
  exact hs.add_section ht

lemma ContMDiffOn.add_section (hs : CMDiff[u] n (T% s)) (ht : CMDiff[u] n (T% t)) :
    CMDiff[u] n (T% (s + t)) :=
  fun x₀ hx₀ ↦ (hs x₀ hx₀).add_section (ht x₀ hx₀)

lemma ContMDiff.add_section (hs : CMDiff n (T% s)) (ht : CMDiff n (T% t)) :
    CMDiff n (T% (s + t)) :=
  fun x₀ ↦ (hs x₀).add_section (ht x₀)

lemma ContMDiffWithinAt.neg_section
    (hs : CMDiffAt[u] n (T% s) x₀) : CMDiffAt[u] n (T% (-s)) x₀ := by
  rw [contMDiffWithinAt_section] at hs ⊢
  set e := trivializationAt F V x₀
  refine hs.neg.congr_of_eventuallyEq ?_ ?_
  · apply eventually_of_mem (U := e.baseSet)
    · exact mem_nhdsWithin_of_mem_nhds <|
        (e.open_baseSet.mem_nhds <| mem_baseSet_trivializationAt F V x₀)
    · intro x hx
      apply (e.linear 𝕜 hx).map_neg
  · apply (e.linear 𝕜 (FiberBundle.mem_baseSet_trivializationAt' x₀)).map_neg

lemma ContMDiffAt.neg_section (hs : CMDiffAt n (T% s) x₀) : CMDiffAt n (T% (-s)) x₀ := by
  rw [← contMDiffWithinAt_univ] at hs ⊢
  exact hs.neg_section

lemma ContMDiffOn.neg_section (hs : CMDiff[u] n (T% s)) : CMDiff[u] n (T% (-s)) :=
  fun x₀ hx₀ ↦ (hs x₀ hx₀).neg_section

lemma ContMDiff.neg_section (hs : CMDiff n (T% s)) : CMDiff n (T% (-s)) :=
  fun x₀ ↦ (hs x₀).neg_section

lemma ContMDiffWithinAt.sub_section (hs : CMDiffAt[u] n (T% s) x₀) (ht : CMDiffAt[u] n (T% t) x₀) :
    CMDiffAt[u] n (T% (s - t)) x₀ := by
  rw [sub_eq_add_neg]
  exact hs.add_section ht.neg_section

lemma ContMDiffAt.sub_section (hs : CMDiffAt n (T% s) x₀) (ht : CMDiffAt n (T% t) x₀) :
    CMDiffAt n (T% (s - t)) x₀ := by
  rw [sub_eq_add_neg]
  apply hs.add_section ht.neg_section

lemma ContMDiffOn.sub_section (hs : CMDiff[u] n (T% s)) (ht : CMDiff[u] n (T% t)) :
    CMDiff[u] n (T% (s - t)) :=
  fun x₀ hx₀ ↦ (hs x₀ hx₀).sub_section (ht x₀ hx₀)

lemma ContMDiff.sub_section (hs : CMDiff n (T% s)) (ht : CMDiff n (T% t)) : CMDiff n (T% (s - t)) :=
  fun x₀ ↦ (hs x₀).sub_section (ht x₀)

lemma ContMDiffWithinAt.smul_section (hf : CMDiffAt[u] n f x₀) (hs : CMDiffAt[u] n (T% s) x₀) :
    CMDiffAt[u] n (T% (f • s)) x₀ := by
  rw [contMDiffWithinAt_section] at hs ⊢
  set e := trivializationAt F V x₀
  refine (hf.smul hs).congr_of_eventuallyEq ?_ ?_
  · apply eventually_of_mem (U := e.baseSet)
    · exact mem_nhdsWithin_of_mem_nhds <|
        (e.open_baseSet.mem_nhds <| mem_baseSet_trivializationAt F V x₀)
    · intro x hx
      apply (e.linear 𝕜 hx).2
  · apply (e.linear 𝕜 (FiberBundle.mem_baseSet_trivializationAt' x₀)).2

lemma ContMDiffAt.smul_section (hf : CMDiffAt n f x₀) (hs : CMDiffAt n (T% s) x₀) :
    CMDiffAt n (T% (f • s)) x₀ := by
  rw [← contMDiffWithinAt_univ] at hs ⊢
  exact .smul_section hf hs

lemma ContMDiffOn.smul_section (hf : CMDiff[u] n f) (hs : CMDiff[u] n (T% s)) :
    CMDiff[u] n (T% (f • s)) :=
  fun x₀ hx₀ ↦ (hf x₀ hx₀).smul_section (hs x₀ hx₀)

lemma ContMDiff.smul_section (hf : CMDiff n f) (hs : CMDiff n (T% s)) : CMDiff n (T% (f • s)) :=
  fun x₀ ↦ (hf x₀).smul_section (hs x₀)

lemma ContMDiffWithinAt.const_smul_section
    (hs : CMDiffAt[u] n (T% s) x₀) : CMDiffAt[u] n (T% (a • s)) x₀ :=
  contMDiffWithinAt_const.smul_section hs

lemma ContMDiffAt.const_smul_section (hs : CMDiffAt n (T% s) x₀) : CMDiffAt n (T% (a • s)) x₀ :=
  contMDiffAt_const.smul_section hs

lemma ContMDiffOn.const_smul_section (hs : CMDiff[u] n (T% s)) : CMDiff[u] n (T% (a • s)) :=
  contMDiffOn_const.smul_section hs

lemma ContMDiff.const_smul_section (hs : CMDiff n (T% s)) : CMDiff n (T% (a • s)) :=
  fun x₀ ↦ (hs x₀).const_smul_section

variable {ι : Type*} {t : ι → (x : M) → V x}

lemma ContMDiffWithinAt.sum_section {s : Finset ι}
    (hs : ∀ i ∈ s, CMDiffAt[u] n (T% (t i ·)) x₀) :
    CMDiffAt[u] n (T% (fun x ↦ (∑ i ∈ s, (t i x)))) x₀ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty] using contMDiffWithinAt_zeroSection ..
  | insert i s hi h =>
    simp only [Finset.sum_insert hi]
    apply (hs _ (s.mem_insert_self i)).add_section
    exact h fun i a ↦ hs _ (s.mem_insert_of_mem a)

lemma ContMDiffAt.sum_section {s : Finset ι}
    (hs : ∀ i ∈ s, CMDiffAt n (T% (t i ·)) x₀) :
    CMDiffAt n (T% (fun x ↦ (∑ i ∈ s, (t i x)))) x₀ := by
  simp_rw [← contMDiffWithinAt_univ] at hs ⊢
  exact .sum_section hs

lemma ContMDiffOn.sum_section {s : Finset ι}
    (hs : ∀ i ∈ s, CMDiff[u] n (T% (t i ·))) :
    CMDiff[u] n (T% (fun x ↦ (∑ i ∈ s, (t i x)))) :=
  fun x₀ hx₀ ↦ .sum_section fun i hi ↦ hs i hi x₀ hx₀

lemma ContMDiff.sum_section {s : Finset ι} (hs : ∀ i ∈ s, CMDiff n (T% (t i ·))) :
    CMDiff n (T% (fun x ↦ (∑ i ∈ s, (t i x)))) :=
  fun x₀ ↦ .sum_section fun i hi ↦ (hs i hi) x₀

lemma ContMDiffOn.smul_section_of_tsupport {s : Π (x : M), V x} {ψ : M → 𝕜} (hψ : CMDiff[u] n ψ)
    (ht : IsOpen u) (ht' : tsupport ψ ⊆ u) (hs : CMDiff[u] n (T% s)) :
    CMDiff n (T% (ψ • s)) := by
  apply contMDiff_of_contMDiffOn_union_of_isOpen (hψ.smul_section hs) ?_ ?_ ht
      (isOpen_compl_iff.mpr <| isClosed_tsupport ψ)
  · apply ((contMDiff_zeroSection _ _).contMDiffOn (s := (tsupport ψ)ᶜ)).congr
    intro y hy
    simp [image_eq_zero_of_notMem_tsupport hy, zeroSection]
  · exact Set.compl_subset_iff_union.mp <| Set.compl_subset_compl.mpr ht'

-- DISSOLVED: ContMDiffWithinAt.sum_section_of_locallyFinite

-- DISSOLVED: ContMDiffAt.sum_section_of_locallyFinite

-- DISSOLVED: ContMDiffOn.sum_section_of_locallyFinite

-- DISSOLVED: ContMDiff.sum_section_of_locallyFinite

-- DISSOLVED: ContMDiffWithinAt.finsum_section_of_locallyFinite

-- DISSOLVED: ContMDiffAt.finsum_section_of_locallyFinite

-- DISSOLVED: ContMDiffOn.finsum_section_of_locallyFinite

-- DISSOLVED: ContMDiff.finsum_section_of_locallyFinite

end operations

structure ContMDiffSection where
  /-- the underlying function of this section -/
  protected toFun : ∀ x, V x
  /-- proof that this section is `C^n` -/
  protected contMDiff_toFun : CMDiff n (T% toFun)
