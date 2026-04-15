/-
Extracted from LinearAlgebra/LinearIndependent/Lemmas.lean
Genuine: 19 of 20 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Linear independence

This file collects consequences of linear (in)dependence and includes specialized tests for
specific families of vectors, requiring more theory to state.

## Main statements

We prove several specialized tests for linear independence of families of vectors and of sets of
vectors.

* `linearIndependent_option`, `linearIndependent_finCons`,
  `linearIndependent_finSucc`: type-specific tests for linear
  independence of families of vector fields;
* `linearIndependent_insert`, `linearIndependent_pair`: linear independence tests for set operations

In many cases we additionally provide dot-style operations (e.g., `LinearIndependent.union`) to
make the linear independence tests usable as `hv.insert ha` etc.

We also prove that, when working over a division ring,
any family of vectors includes a linear independent subfamily spanning the same subspace.

## TODO

Rework proofs to hold in semirings, by avoiding the path through
`ker (Finsupp.linearCombination R v) = ⊥`.

## Tags

linearly dependent, linear dependence, linearly independent, linear independence

-/

assert_not_exists Cardinal

noncomputable section

open Function Module Set Submodule

universe u' u

variable {ι : Type u'} {ι' : Type*} {R : Type*} {K : Type*} {s : Set ι}

variable {M : Type*} {M' : Type*} {V : Type u}

section Semiring

variable {v : ι → M}

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M']

variable [Module R M] [Module R M']

variable (R) (v)

variable {R v}

theorem Fintype.linearIndependent_iff'ₛ [Fintype ι] [DecidableEq ι] :
    LinearIndependent R v ↔
      Injective (LinearMap.lsum R (fun _ ↦ R) ℕ fun i ↦ LinearMap.id.smulRight (v i)) := by
  simp [Fintype.linearIndependent_iffₛ, Injective, funext_iff]

lemma LinearIndependent.pair_iffₛ {x y : M} :
    LinearIndependent R ![x, y] ↔
      ∀ (s t s' t' : R), s • x + t • y = s' • x + t' • y → s = s' ∧ t = t' := by
  simp [Fintype.linearIndependent_iffₛ, Fin.forall_fin_two, ← FinVec.forall_iff]; rfl

lemma LinearIndependent.eq_of_pair {x y : M} (h : LinearIndependent R ![x, y])
    {s t s' t' : R} (h' : s • x + t • y = s' • x + t' • y) : s = s' ∧ t = t' :=
  pair_iffₛ.mp h _ _ _ _ h'

lemma LinearIndependent.eq_zero_of_pair' {x y : M} (h : LinearIndependent R ![x, y])
    {s t : R} (h' : s • x = t • y) : s = 0 ∧ t = 0 := by
  suffices H : s = 0 ∧ 0 = t from ⟨H.1, H.2.symm⟩
  exact h.eq_of_pair (by simpa using h')

lemma LinearIndependent.eq_zero_of_pair {x y : M} (h : LinearIndependent R ![x, y])
    {s t : R} (h' : s • x + t • y = 0) : s = 0 ∧ t = 0 := by
  replace h := @h (.single 0 s + .single 1 t) 0 ?_
  · exact ⟨by simpa using congr($h 0), by simpa using congr($h 1)⟩
  simpa

section Indexed

theorem linearIndepOn_iUnion_of_directed {η : Type*} {s : η → Set ι} (hs : Directed (· ⊆ ·) s)
    (h : ∀ i, LinearIndepOn R v (s i)) : LinearIndepOn R v (⋃ i, s i) := by
  by_cases hη : Nonempty η
  · refine linearIndepOn_of_finite (⋃ i, s i) fun t ht ft => ?_
    rcases finite_subset_iUnion ft ht with ⟨I, fi, hI⟩
    rcases hs.finset_le fi.toFinset with ⟨i, hi⟩
    exact (h i).mono (Subset.trans hI <| iUnion₂_subset fun j hj => hi j (fi.mem_toFinset.2 hj))
  · refine (linearIndepOn_empty R v).mono (t := iUnion (s ·)) ?_
    rintro _ ⟨_, ⟨i, _⟩, _⟩
    exact hη ⟨i⟩

theorem linearIndepOn_sUnion_of_directed {s : Set (Set ι)} (hs : DirectedOn (· ⊆ ·) s)
    (h : ∀ a ∈ s, LinearIndepOn R v a) : LinearIndepOn R v (⋃₀ s) := by
  rw [sUnion_eq_iUnion]
  exact linearIndepOn_iUnion_of_directed hs.directed_val (by simpa using h)

theorem linearIndepOn_biUnion_of_directed {η} {s : Set η} {t : η → Set ι}
    (hs : DirectedOn (t ⁻¹'o (· ⊆ ·)) s) (h : ∀ a ∈ s, LinearIndepOn R v (t a)) :
    LinearIndepOn R v (⋃ a ∈ s, t a) := by
  rw [biUnion_eq_iUnion]
  exact linearIndepOn_iUnion_of_directed (directed_comp.2 <| hs.directed_val) (by simpa using h)

end Indexed

section repr

variable (ι R M) in

theorem iSupIndep_range_lsingle :
    iSupIndep fun i : ι ↦ LinearMap.range (Finsupp.lsingle (R := R) (M := M) i) := by
  refine fun i ↦ disjoint_iff_inf_le.mpr ?_
  rintro x ⟨⟨m, rfl⟩, hm⟩
  suffices ⨆ j ≠ i, LinearMap.range (Finsupp.lsingle j) ≤ Finsupp.supported M R {i}ᶜ by
    have := (Finsupp.mem_supported ..).mp (this hm); simp_all
  refine iSup₂_le fun j ne ↦ ?_
  rintro _ ⟨m, rfl⟩
  simp [Finsupp.mem_supported, ne]

theorem LinearMap.iSupIndep_map (f : M →ₗ[R] M') (inj : Injective f) {m : ι → Submodule R M}
    (ind : iSupIndep m) : iSupIndep fun i ↦ (m i).map f := by
  simp_rw [iSupIndep, disjoint_iff_inf_le] at ind ⊢
  rintro i _ ⟨⟨x, hxi, rfl⟩, hx⟩
  rw [ind i ⟨hxi, _⟩]; · simp
  simp_rw [← Submodule.map_iSup] at hx
  have ⟨y, hy, eq⟩ := hx
  simpa [← inj eq]

variable (hv : LinearIndependent R v)

theorem LinearIndependent.iSupIndep_span_singleton (hv : LinearIndependent R v) :
    iSupIndep fun i => R ∙ v i := by
  convert LinearMap.iSupIndep_map _ hv (iSupIndep_range_lsingle ι R R)
  ext; simp [mem_span_singleton]

end repr

section union

open LinearMap Finsupp

theorem linearIndependent_inl_union_inr' {v : ι → M} {v' : ι' → M'}
    (hv : LinearIndependent R v) (hv' : LinearIndependent R v') :
    LinearIndependent R (Sum.elim (inl R M M' ∘ v) (inr R M M' ∘ v')) := by
  have : linearCombination R (Sum.elim (inl R M M' ∘ v) (inr R M M' ∘ v')) =
      .prodMap (linearCombination R v) (linearCombination R v') ∘ₗ
      (sumFinsuppLEquivProdFinsupp R).toLinearMap := by ext (_ | _) <;> simp
  rw [LinearIndependent, this]
  simpa [LinearMap.coe_prodMap] using ⟨hv, hv'⟩

theorem LinearIndependent.inl_union_inr {s : Set M} {t : Set M'}
    (hs : LinearIndependent R (fun x => x : s → M))
    (ht : LinearIndependent R (fun x => x : t → M')) :
    LinearIndependent R (fun x => x : ↥(inl R M M' '' s ∪ inr R M M' '' t) → M × M') := by
  nontriviality R
  let e : s ⊕ t ≃ ↥(inl R M M' '' s ∪ inr R M M' '' t) :=
    .ofBijective (Sum.elim (fun i ↦ ⟨_, .inl ⟨_, i.2, rfl⟩⟩) fun i ↦ ⟨_, .inr ⟨_, i.2, rfl⟩⟩)
      ⟨by rintro (_ | _) (_ | _) eq <;> simp [hs.ne_zero, ht.ne_zero] at eq <;> aesop,
        by rintro ⟨_, ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩⟩ <;> aesop⟩
  refine (linearIndependent_equiv' e ?_).mp (linearIndependent_inl_union_inr' hs ht)
  ext (_ | _) <;> rfl

end union

section Maximal

universe v w

variable (R)

theorem exists_maximal_linearIndepOn' (v : ι → M) :
    ∃ s : Set ι, (LinearIndepOn R v s) ∧ ∀ t : Set ι, s ⊆ t → (LinearIndepOn R v t) → s = t := by
  let indep : Set ι → Prop := fun s => LinearIndepOn R v s
  let X := { I : Set ι // indep I }
  let r : X → X → Prop := fun I J => I.1 ⊆ J.1
  have key : ∀ c : Set X, IsChain r c → indep (⋃ (I : X) (_ : I ∈ c), I) := by
    intro c hc
    dsimp [indep]
    rw [linearIndepOn_iffₛ]
    intro f hfsupp g hgsupp hsum
    rcases eq_empty_or_nonempty c with (rfl | hn)
    · rw [show f = 0 by simpa using hfsupp, show g = 0 by simpa using hgsupp]
    haveI : Std.Refl r := ⟨fun _ => Set.Subset.refl _⟩
    classical
    obtain ⟨I, _I_mem, hI⟩ : ∃ I ∈ c, (f.support ∪ g.support : Set ι) ⊆ I :=
      f.support.coe_union _ ▸ hc.directedOn.exists_mem_subset_of_finset_subset_biUnion hn <| by
        simpa using And.intro hfsupp hgsupp
    exact linearIndepOn_iffₛ.mp I.2 f (subset_union_left.trans hI)
      g (subset_union_right.trans hI) hsum
  obtain ⟨⟨I, hli : indep I⟩, hmax : ∀ a, r ⟨I, hli⟩ a → r a ⟨I, hli⟩⟩ :=
    exists_maximal_of_chains_bounded (r := r)
      (fun c hc => ⟨⟨⋃ I ∈ c, (I : Set ι), key c hc⟩, fun I => Set.subset_biUnion_of_mem⟩)
      Set.Subset.trans
  exact ⟨I, hli, fun J hsub hli => Set.Subset.antisymm hsub (hmax ⟨J, hli⟩ hsub)⟩

end Maximal

lemma Submodule.codisjoint_span_image_of_codisjoint (hv : Submodule.span R (Set.range v) = ⊤)
    {s t : Set ι} (hst : Codisjoint s t) :
    Codisjoint (Submodule.span R (v '' s)) (Submodule.span R (v '' t)) := by
  rw [Finsupp.span_image_eq_map_linearCombination, Finsupp.span_image_eq_map_linearCombination]
  refine Submodule.codisjoint_map ?_ (Finsupp.codisjoint_supported_supported hst)
  rwa [← LinearMap.range_eq_top, Finsupp.range_linearCombination]

lemma LinearIndependent.isCompl_span_image (h₁ : LinearIndependent R v)
    (h₂ : Submodule.span R (Set.range v) = ⊤) {s t : Set ι} (hst : IsCompl s t) :
    IsCompl (Submodule.span R (v '' s)) (Submodule.span R (v '' t)) :=
  ⟨h₁.disjoint_span_image hst.1, Submodule.codisjoint_span_image_of_codisjoint h₂ hst.2⟩

end Semiring

section Module

variable {v : ι → M}

variable [Ring R] [AddCommGroup M] [AddCommGroup M']

variable [Module R M] [Module R M']

theorem Fintype.linearIndependent_iff' [Fintype ι] [DecidableEq ι] :
    LinearIndependent R v ↔
      LinearMap.ker (LinearMap.lsum R (fun _ ↦ R) ℕ fun i ↦ LinearMap.id.smulRight (v i)) = ⊥ := by
  simp [Fintype.linearIndependent_iff, LinearMap.ker_eq_bot', funext_iff]

section Pair

variable {x y : M}

lemma LinearIndependent.pair_iff :
    LinearIndependent R ![x, y] ↔ ∀ (s t : R), s • x + t • y = 0 → s = 0 ∧ t = 0 := by
  rw [← linearIndepOn_univ_iff, ← Finset.coe_univ, show @Finset.univ (Fin 2) _ = {0,1} from rfl,
    Finset.coe_insert, Finset.coe_singleton, LinearIndepOn.pair_iff _ (by trivial)]
  simp

lemma LinearIndependent.pair_symm_iff :
    LinearIndependent R ![x, y] ↔ LinearIndependent R ![y, x] := by
  suffices ∀ x y : M, LinearIndependent R ![x, y] → LinearIndependent R ![y, x] by tauto
  simp only [LinearIndependent.pair_iff]
  intro x y h s t
  specialize h t s
  rwa [add_comm, and_comm]
