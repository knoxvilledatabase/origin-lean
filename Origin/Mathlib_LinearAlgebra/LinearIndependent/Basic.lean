/-
Extracted from LinearAlgebra/LinearIndependent/Basic.lean
Genuine: 14 of 14 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Linear independence

This file collects basic consequences of linear (in)dependence and includes specialized tests for
specific families of vectors.

## Main statements

We prove several specialized tests for linear independence of families of vectors and of sets of
vectors.

* `linearIndependent_empty_type`: a family indexed by an empty type is linearly independent;
* `linearIndependent_unique_iff`: if `ι` is a singleton, then `LinearIndependent K v` is
  equivalent to `v default ≠ 0`;
* `linearIndependent_sum`: type-specific test for linear independence of families of vector
  fields;
* `linearIndependent_singleton`: linear independence tests for set operations.

In many cases we additionally provide dot-style operations (e.g., `LinearIndependent.union`) to
make the linear independence tests usable as `hv.insert ha` etc.

## TODO

Rework proofs to hold in semirings, by avoiding the path through
`ker (Finsupp.linearCombination R v) = ⊥`.

## Tags

linearly dependent, linear dependence, linearly independent, linear independence

-/

assert_not_exists Cardinal

noncomputable section

open Function Set Submodule

universe u' u

variable {ι : Type u'} {ι' : Type*} {R : Type*} {K : Type*} {s : Set ι}

variable {M : Type*} {M' : Type*} {V : Type u}

section Semiring

variable {v : ι → M}

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M']

variable [Module R M] [Module R M']

variable (R) (v)

variable {R v}

theorem LinearIndependent.restrict_scalars [Semiring K] [SMulWithZero R K] [Module K M]
    [IsScalarTower R K M] (hinj : Injective fun r : R ↦ r • (1 : K))
    (li : LinearIndependent K v) : LinearIndependent R v := by
  intro x y hxy
  let f := fun r : R => r • (1 : K)
  have := @li (x.mapRange f (by simp [f])) (y.mapRange f (by simp [f])) ?_
  · ext i
    exact hinj congr($this i)
  simpa [Finsupp.linearCombination, f, Finsupp.sum_mapRange_index]

variable (R) in

theorem LinearIndependent.restrict_scalars' [Semiring K] [SMulWithZero R K] [Module K M]
    [IsScalarTower R K M] [FaithfulSMul R K] [IsScalarTower R K K] {v : ι → M}
    (li : LinearIndependent K v) : LinearIndependent R v :=
  restrict_scalars ((faithfulSMul_iff_injective_smul_one R K).mp inferInstance) li

theorem Submodule.range_ker_disjoint {f : M →ₗ[R] M'}
    (hv : LinearIndependent R (f ∘ v)) :
    Disjoint (span R (range v)) (LinearMap.ker f) := by
  rw [LinearIndependent, Finsupp.linearCombination_linear_comp] at hv
  rw [disjoint_iff_inf_le, ← Set.image_univ, Finsupp.span_image_eq_map_linearCombination,
    map_inf_eq_map_inf_comap, (LinearMap.ker_comp _ _).symm.trans
      (LinearMap.ker_eq_bot_of_injective hv), inf_bot_eq, map_bot]

theorem LinearIndependent.map_of_injective_injectiveₛ {R' M' : Type*}
    [Semiring R'] [AddCommMonoid M'] [Module R' M'] (hv : LinearIndependent R v)
    (i : R' → R) (j : M →+ M') (hi : Injective i) (hj : Injective j)
    (hc : ∀ (r : R') (m : M), j (i r • m) = r • j m) : LinearIndependent R' (j ∘ v) := by
  rw [linearIndependent_iff'ₛ] at hv ⊢
  intro S r₁ r₂ H s hs
  simp_rw [comp_apply, ← hc, ← map_sum] at H
  exact hi <| hv _ _ _ (hj H) s hs

theorem LinearIndependent.map_of_surjective_injectiveₛ {R' M' : Type*}
    [Semiring R'] [AddCommMonoid M'] [Module R' M'] (hv : LinearIndependent R v)
    (i : R → R') (j : M →+ M') (hi : Surjective i) (hj : Injective j)
    (hc : ∀ (r : R) (m : M), j (r • m) = i r • j m) : LinearIndependent R' (j ∘ v) := by
  obtain ⟨i', hi'⟩ := hi.hasRightInverse
  refine hv.map_of_injective_injectiveₛ i' j (fun _ _ h ↦ ?_) hj fun r m ↦ ?_
  · apply_fun i at h
    rwa [hi', hi'] at h
  rw [hc (i' r) m, hi']

theorem LinearIndependent.map_injOn (hv : LinearIndependent R v) (f : M →ₗ[R] M')
    (hf_inj : Set.InjOn f (span R (Set.range v))) : LinearIndependent R (f ∘ v) :=
  (f.linearIndependent_iff_of_injOn hf_inj).mpr hv

theorem LinearIndepOn.map_injOn (hv : LinearIndepOn R v s) (f : M →ₗ[R] M')
    (hf_inj : Set.InjOn f (span R (v '' s))) : LinearIndepOn R (f ∘ v) s :=
  (f.linearIndepOn_iff_of_injOn hf_inj).mpr hv

theorem LinearIndepOn.comp_of_image {s : Set ι'} {f : ι' → ι} (h : LinearIndepOn R v (f '' s))
    (hf : InjOn f s) : LinearIndepOn R (v ∘ f) s :=
  LinearIndependent.comp h _ (Equiv.Set.imageOfInjOn _ _ hf).injective

theorem LinearIndepOn.image_of_comp (f : ι → ι') (g : ι' → M) (hs : LinearIndepOn R (g ∘ f) s) :
    LinearIndepOn R g (f '' s) := by
  nontriviality R
  have : InjOn f s := injOn_iff_injective.2 hs.injective.of_comp
  exact (linearIndependent_equiv' (Equiv.Set.imageOfInjOn f s this) rfl).1 hs

theorem LinearIndepOn.id_image (hs : LinearIndepOn R v s) : LinearIndepOn R id (v '' s) :=
  LinearIndepOn.image_of_comp v id hs

theorem LinearIndepOn_iff_linearIndepOn_image_injOn [Nontrivial R] :
    LinearIndepOn R v s ↔ LinearIndepOn R id (v '' s) ∧ InjOn v s :=
  ⟨fun h ↦ ⟨h.id_image, h.injOn⟩, fun h ↦ (linearIndepOn_iff_image h.2).2 h.1⟩

theorem linearIndepOn_congr {w : ι → M} (h : EqOn v w s) :
    LinearIndepOn R v s ↔ LinearIndepOn R w s := by
  rw [LinearIndepOn, LinearIndepOn]
  convert Iff.rfl using 2
  ext x
  exact h.symm x.2

theorem LinearIndepOn.congr {w : ι → M} (hli : LinearIndepOn R v s) (h : EqOn v w s) :
    LinearIndepOn R w s :=
  (linearIndepOn_congr h).1 hli

theorem LinearIndependent.group_smul {G : Type*} [hG : Group G] [MulAction G R]
    [SMul G M] [IsScalarTower G R M] [SMulCommClass G R M] {v : ι → M}
    (hv : LinearIndependent R v) (w : ι → G) : LinearIndependent R (w • v) := by
  rw [linearIndependent_iff''ₛ] at hv ⊢
  intro s g₁ g₂ hgs hsum i
  refine (Group.isUnit (w i)).smul_left_cancel.mp ?_
  refine hv s (fun i ↦ w i • g₁ i) (fun i ↦ w i • g₂ i) (fun i hi ↦ ?_) ?_ i
  · simp_rw [hgs i hi]
  · simpa only [smul_assoc, smul_comm] using hsum
