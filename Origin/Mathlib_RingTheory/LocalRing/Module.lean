/-
Extracted from RingTheory/LocalRing/Module.lean
Genuine: 13 of 13 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Finite modules over local rings

This file gathers various results about finite modules over a local ring `(R, 𝔪, k)`.

## Main results
- `IsLocalRing.subsingleton_tensorProduct`: If `M` is finitely generated, `k ⊗ M = 0 ↔ M = 0`.
- `Module.free_of_maximalIdeal_rTensor_injective`:
  If `M` is a finitely presented module such that `m ⊗ M → M` is injective
  (for example when `M` is flat), then `M` is free.
- `Module.free_of_lTensor_residueField_injective`: If `N → M → P → 0` is a presentation of `P` with
  `N` finite and `M` finite free, then injectivity of `k ⊗ N → k ⊗ M` implies that `P` is free.
- `IsLocalRing.split_injective_iff_lTensor_residueField_injective`:
  Given an `R`-linear map `l : M → N` with `M` finite and `N` finite free,
  `l` is a split injection if and only if `k ⊗ l` is a (split) injection.
-/

open Module

universe u

variable {R M N P : Type*} [CommRing R]

variable [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

open Function (Injective Surjective Exact)

open IsLocalRing TensorProduct

local notation "k" => ResidueField R

local notation "𝔪" => maximalIdeal R

variable [AddCommGroup P] [Module R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P)

namespace IsLocalRing

variable [IsLocalRing R]

theorem map_mkQ_eq {N₁ N₂ : Submodule R M} (h : N₁ ≤ N₂) (h' : N₂.FG) :
    N₁.map (Submodule.mkQ (𝔪 • N₂)) = N₂.map (Submodule.mkQ (𝔪 • N₂)) ↔ N₁ = N₂ := by
  constructor
  · intro hN
    have : N₂ ≤ 𝔪 • N₂ ⊔ N₁ := by
      simpa using Submodule.comap_mono (f := Submodule.mkQ (𝔪 • N₂)) hN.ge
    rw [sup_comm] at this
    exact h.antisymm (Submodule.le_of_le_smul_of_le_jacobson_bot h'
      (by rw [jacobson_eq_maximalIdeal]; exact bot_ne_top) this)
  · rintro rfl; simp

theorem map_mkQ_eq_top {N : Submodule R M} [Module.Finite R M] :
    N.map (Submodule.mkQ (𝔪 • ⊤)) = ⊤ ↔ N = ⊤ := by
  rw [← map_mkQ_eq (N₁ := N) le_top Module.Finite.fg_top, Submodule.map_top, Submodule.range_mkQ]

theorem map_tensorProduct_mk_eq_top {N : Submodule R M} [Module.Finite R M] :
    N.map (TensorProduct.mk R k M 1) = ⊤ ↔ N = ⊤ := by
  constructor
  · intro hN
    letI : Module k (M ⧸ (𝔪 • ⊤ : Submodule R M)) :=
      inferInstanceAs (Module (R ⧸ 𝔪) (M ⧸ 𝔪 • (⊤ : Submodule R M)))
    letI : IsScalarTower R k (M ⧸ (𝔪 • ⊤ : Submodule R M)) :=
      inferInstanceAs (IsScalarTower R (R ⧸ 𝔪) (M ⧸ 𝔪 • (⊤ : Submodule R M)))
    let f := AlgebraTensorModule.lift (((LinearMap.ringLmapEquivSelf k k _).symm
      (Submodule.mkQ (𝔪 • ⊤ : Submodule R M))).restrictScalars R)
    have : f.comp (TensorProduct.mk R k M 1) = Submodule.mkQ (𝔪 • ⊤) := by ext; simp [f]
    have hf : Function.Surjective f := by
      intro x; obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
      rw [← this, LinearMap.comp_apply]; exact ⟨_, rfl⟩
    apply_fun Submodule.map f at hN
    rwa [← Submodule.map_comp, this, Submodule.map_top, LinearMap.range_eq_top.2 hf,
      map_mkQ_eq_top] at hN
  · rintro rfl; rw [Submodule.map_top, LinearMap.range_eq_top]
    exact TensorProduct.mk_surjective R M k Ideal.Quotient.mk_surjective

theorem subsingleton_tensorProduct [Module.Finite R M] :
    Subsingleton (k ⊗[R] M) ↔ Subsingleton M := by
  rw [← Submodule.subsingleton_iff R, ← subsingleton_iff_bot_eq_top,
    ← Submodule.subsingleton_iff R, ← subsingleton_iff_bot_eq_top,
    ← map_tensorProduct_mk_eq_top (M := M), Submodule.map_bot]

theorem span_eq_top_of_tmul_eq_basis [Module.Finite R M] {ι}
    (f : ι → M) (b : Basis ι k (k ⊗[R] M))
    (hb : ∀ i, 1 ⊗ₜ f i = b i) : Submodule.span R (Set.range f) = ⊤ := by
  rw [← map_tensorProduct_mk_eq_top, Submodule.map_span, ← Submodule.restrictScalars_span R k
    Ideal.Quotient.mk_surjective, Submodule.restrictScalars_eq_top_iff,
    ← b.span_eq, ← Set.range_comp]
  simp only [Function.comp_def, mk_apply, hb, Basis.span_eq]

end IsLocalRing

lemma Module.mem_support_iff_nontrivial_residueField_tensorProduct [Module.Finite R M]
    (p : PrimeSpectrum R) :
    p ∈ Module.support R M ↔ Nontrivial (p.asIdeal.ResidueField ⊗[R] M) := by
  let K := p.asIdeal.ResidueField
  let e := (AlgebraTensorModule.cancelBaseChange R (Localization.AtPrime p.asIdeal) K K M).symm
  rw [e.nontrivial_congr, Module.mem_support_iff,
    (LocalizedModule.equivTensorProduct p.asIdeal.primeCompl M).nontrivial_congr,
    ← not_iff_not, not_nontrivial_iff_subsingleton, not_nontrivial_iff_subsingleton,
    IsLocalRing.subsingleton_tensorProduct]

open Function in

theorem lTensor_injective_of_exact_of_exact_of_rTensor_injective
    {M₁ M₂ M₃ N₁ N₂ N₃}
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]
    [AddCommGroup N₁] [Module R N₁] [AddCommGroup N₂] [Module R N₂] [AddCommGroup N₃] [Module R N₃]
    {f₁ : M₁ →ₗ[R] M₂} {f₂ : M₂ →ₗ[R] M₃} {g₁ : N₁ →ₗ[R] N₂} {g₂ : N₂ →ₗ[R] N₃}
    (hfexact : Exact f₁ f₂) (hfsurj : Surjective f₂)
    (hgexact : Exact g₁ g₂) (hgsurj : Surjective g₂)
    (hfinj : Injective (f₁.rTensor N₃)) (hginj : Injective (g₁.lTensor M₂)) :
    Injective (g₁.lTensor M₃) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨x, rfl⟩ := f₂.rTensor_surjective N₁ hfsurj x
  have : f₂.rTensor N₂ (g₁.lTensor M₂ x) = 0 := by
    rw [← hx, ← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
      LinearMap.lTensor_comp_rTensor]
  obtain ⟨y, hy⟩ := (rTensor_exact N₂ hfexact hfsurj _).mp this
  have : g₂.lTensor M₁ y = 0 := by
    apply hfinj
    trans g₂.lTensor M₂ (g₁.lTensor M₂ x)
    · rw [← hy, ← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
        LinearMap.lTensor_comp_rTensor]
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hgexact.linearMap_comp_eq_zero]
    simp
  obtain ⟨z, rfl⟩ := (lTensor_exact _ hgexact hgsurj _).mp this
  obtain rfl : f₁.rTensor N₁ z = x := by
    apply hginj
    simp only [← hy, ← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor,
      LinearMap.rTensor_comp_lTensor]
  rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hfexact.linearMap_comp_eq_zero]
  simp

namespace Module

variable [IsLocalRing R]

set_option backward.isDefEq.respectTransparency false in

lemma exists_basis_of_basis_baseChange [Module.FinitePresentation R M]
    {ι : Type*} (v : ι → M) (hli : LinearIndependent k (TensorProduct.mk R k M 1 ∘ v))
    (hsp : Submodule.span k (Set.range (TensorProduct.mk R k M 1 ∘ v)) = ⊤)
    (H : Function.Injective ((𝔪).subtype.rTensor M)) :
    ∃ (b : Basis ι R M), ∀ i, b i = v i := by
  let bk : Basis ι k (k ⊗[R] M) := Basis.mk hli (by rw [hsp])
  haveI : Finite ι := Module.Finite.finite_basis bk
  letI : Fintype ι := Fintype.ofFinite ι
  let i := Finsupp.linearCombination R v
  have hi : Surjective i := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    refine IsLocalRing.span_eq_top_of_tmul_eq_basis (R := R) (f := v) bk
      (fun _ ↦ by simp [bk])
  have : Module.Finite R (LinearMap.ker i) :=
    .of_fg (Module.FinitePresentation.fg_ker i hi)
  -- We claim that `i` is actually a bijection,
  -- hence `v` induces an isomorphism `M ≃[R] Rᴵ` showing that `v` is a basis.
  let iequiv : (ι →₀ R) ≃ₗ[R] M := by
    refine LinearEquiv.ofBijective i ⟨?_, hi⟩
    -- By Nakayama's lemma, it suffices to show that `k ⊗ ker(i) = 0`.
    rw [← LinearMap.ker_eq_bot, ← Submodule.subsingleton_iff_eq_bot,
      ← IsLocalRing.subsingleton_tensorProduct (R := R), subsingleton_iff_forall_eq 0]
    have : Function.Surjective (i.baseChange k) := i.lTensor_surjective _ hi
    -- By construction, `k ⊗ i : kᴵ → k ⊗ M` is bijective.
    have hi' : Function.Bijective (i.baseChange k) := by
      refine ⟨?_, this⟩
      rw [← LinearMap.ker_eq_bot (M := k ⊗[R] (ι →₀ R)) (f := i.baseChange k),
        ← Submodule.finrank_eq_zero (R := k) (M := k ⊗[R] (ι →₀ R)),
        ← Nat.add_right_inj (n := Module.finrank k (LinearMap.range <| i.baseChange k)),
        LinearMap.finrank_range_add_finrank_ker (V := k ⊗[R] (ι →₀ R)),
        LinearMap.range_eq_top.mpr this, finrank_top]
      simp only [Module.finrank_tensorProduct, Module.finrank_self,
        Module.finrank_finsupp_self, one_mul, add_zero]
      rw [Module.finrank_eq_card_basis bk]
    -- On the other hand, `m ⊗ M → M` injective => `Tor₁(k, M) = 0` => `k ⊗ ker(i) → kᴵ` injective.
    intro x
    refine lTensor_injective_of_exact_of_exact_of_rTensor_injective
      (N₁ := LinearMap.ker i) (N₂ := ι →₀ R) (N₃ := M)
      (f₁ := (𝔪).subtype) (f₂ := Submodule.mkQ 𝔪)
      (g₁ := (LinearMap.ker i).subtype) (g₂ := i) (LinearMap.exact_subtype_mkQ 𝔪)
      (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_ker_map i) hi H ?_ ?_
    · apply Module.Flat.lTensor_preserves_injective_linearMap
      exact Subtype.val_injective
    · apply hi'.injective
      rw [LinearMap.baseChange_eq_ltensor]
      erw [← LinearMap.comp_apply (i.lTensor k), ← LinearMap.lTensor_comp]
      rw [(LinearMap.exact_subtype_ker_map i).linearMap_comp_eq_zero]
      simp only [LinearMap.lTensor_zero, LinearMap.zero_apply, map_zero]
  use Basis.ofRepr iequiv.symm
  intro j
  simp [iequiv, i]

lemma exists_basis_of_span_of_maximalIdeal_rTensor_injective [Module.FinitePresentation R M]
    (H : Function.Injective ((𝔪).subtype.rTensor M))
    {ι : Type u} (v : ι → M) (hv : Submodule.span R (Set.range v) = ⊤) :
    ∃ (κ : Type u) (a : κ → ι) (b : Basis κ R M), ∀ i, b i = v (a i) := by
  have := (map_tensorProduct_mk_eq_top (N := Submodule.span R (Set.range v))).mpr hv
  rw [← Submodule.span_image, ← Set.range_comp, eq_top_iff, ← SetLike.coe_subset_coe,
    Submodule.top_coe] at this
  have : Submodule.span k (Set.range (TensorProduct.mk R k M 1 ∘ v)) = ⊤ := by
    rw [eq_top_iff]
    exact Set.Subset.trans this (Submodule.span_subset_span _ _ _)
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' k (TensorProduct.mk R k M 1 ∘ v)
  rw [this] at hsp
  obtain ⟨b, hb⟩ := exists_basis_of_basis_baseChange (v ∘ a) hli hsp H
  use κ, a, b, hb

lemma exists_basis_of_span_of_flat [Module.FinitePresentation R M] [Module.Flat R M]
    {ι : Type u} (v : ι → M) (hv : Submodule.span R (Set.range v) = ⊤) :
    ∃ (κ : Type u) (a : κ → ι) (b : Basis κ R M), ∀ i, b i = v (a i) :=
  exists_basis_of_span_of_maximalIdeal_rTensor_injective
    (Module.Flat.rTensor_preserves_injective_linearMap (𝔪).subtype Subtype.val_injective) v hv

theorem free_of_maximalIdeal_rTensor_injective [Module.FinitePresentation R M]
    (H : Function.Injective ((𝔪).subtype.rTensor M)) :
    Module.Free R M := by
  obtain ⟨_, _, b, _⟩ := exists_basis_of_span_of_maximalIdeal_rTensor_injective H id (by simp)
  exact Free.of_basis b

theorem IsLocalRing.linearIndependent_of_flat [Flat R M] {ι : Type u} (v : ι → M)
    (h : LinearIndependent k (TensorProduct.mk R k M 1 ∘ v)) : LinearIndependent R v := by
  rw [linearIndependent_iff']; intro s f hfv i hi
  classical
  induction s using Finset.induction generalizing v i with
  | empty => exact (Finset.notMem_empty _ hi).elim
  | insert n s hn ih => ?_
  rw [← Finset.sum_coe_sort] at hfv
  have ⟨l, a, y, hay, hfa⟩ := Flat.isTrivialRelation_of_sum_smul_eq_zero hfv
  have : v n ∉ 𝔪 • (⊤ : Submodule R M) := by
    simpa only [← LinearMap.ker_tensorProductMk] using h.ne_zero n
  set n : ↥(insert n s) := ⟨n, Finset.mem_insert_self ..⟩ with n_def
  obtain ⟨j, hj⟩ : ∃ j, IsUnit (a n j) := by
    contrapose! this
    rw [show v n = _ from hay n]
    exact sum_mem fun _ _ ↦ Submodule.smul_mem_smul (this _) ⟨⟩
  let a' (i : ι) : R := if hi : _ then a ⟨i, hi⟩ j else 0
  have a_eq i : a i j = a' i.1 := by simp_rw [a', dif_pos i.2]
  have hfn : f n = -(∑ i ∈ s, f i * a' i) * hj.unit⁻¹ := by
    rw [← hj.mul_left_inj, mul_assoc, hj.val_inv_mul, mul_one, eq_neg_iff_add_eq_zero]
    convert hfa j
    simp_rw [a_eq, Finset.sum_coe_sort _ (fun i ↦ f i * a' i), s.sum_insert hn, n_def]
  let c (i : ι) : R := -(if i = n then 0 else a' i) * hj.unit⁻¹
  specialize ih (v + (c · • v n)) ?_ ?_
  · convert (linearIndependent_add_smul_iff (c := Ideal.Quotient.mk _ ∘ c) (i := n.1) ?_).mpr h
    · ext; simp [tmul_add]; rfl
    simp_rw [Function.comp_def, c, if_pos, neg_zero, zero_mul, map_zero]
  · rw [Finset.sum_coe_sort _ (fun i ↦ f i • v i), s.sum_insert hn, add_comm, hfn] at hfv
    simp_rw [Pi.add_apply, smul_add, s.sum_add_distrib, c, smul_smul, ← s.sum_smul, ← mul_assoc,
      ← s.sum_mul, mul_neg, s.sum_neg_distrib, ← hfv]
    congr 4
    exact s.sum_congr rfl fun i hi ↦ by rw [if_neg (ne_of_mem_of_not_mem hi hn)]
  obtain hi | hi := Finset.mem_insert.mp hi
  · rw [hi, hfn, Finset.sum_eq_zero, neg_zero, zero_mul]
    intro i hi; rw [ih i hi, zero_mul]
  · exact ih i hi

open Finsupp in

theorem IsLocalRing.linearCombination_bijective_of_flat [Module.Finite R M] [Flat R M] {ι : Type u}
    (v : ι → M) (h : Function.Bijective (linearCombination k (TensorProduct.mk R k M 1 ∘ v))) :
    Function.Bijective (linearCombination R v) := by
  use linearIndependent_of_flat _ h.1
  rw [← LinearMap.range_eq_top, range_linearCombination]
  refine span_eq_top_of_tmul_eq_basis _ (.mk h.1 ?_) fun _ ↦ ?_
  · simpa only [top_le_iff, ← range_linearCombination, LinearMap.range_eq_top] using h.2
  · simp
