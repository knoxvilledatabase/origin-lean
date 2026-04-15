/-
Extracted from Analysis/Fourier/AddCircleMulti.lean
Genuine: 13 of 17 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Multivariate Fourier series

In this file we define the Fourier series of an L² function on the `d`-dimensional unit circle, and
show that it converges to the function in the L² norm. We also prove uniform convergence of the
Fourier series if `f` is continuous and the sequence of its Fourier coefficients is summable.
-/

noncomputable section

open scoped ComplexConjugate ENNReal

open Set Algebra Submodule MeasureTheory

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

abbrev UnitAddTorus (d : Type*) := d → UnitAddCircle

namespace UnitAddTorus

variable {d : Type*} [Fintype d]

section Monomials

variable (n : d → ℤ)

def mFourier : C(UnitAddTorus d, ℂ) where
  toFun x := ∏ i : d, fourier (n i) (x i)
  continuous_toFun := by fun_prop

variable {n} {x : UnitAddTorus d}

lemma mFourier_neg : mFourier (-n) x = conj (mFourier n x) := by
  simp only [mFourier, Pi.neg_apply, fourier_neg, ContinuousMap.coe_mk, map_prod]

lemma mFourier_add {m : d → ℤ} : mFourier (m + n) x = mFourier m x * mFourier n x := by
  simp only [mFourier, Pi.add_apply, fourier_add, ContinuousMap.coe_mk, ← Finset.prod_mul_distrib]

lemma mFourier_zero : mFourier (0 : d → ℤ) = 1 := by
  ext x
  simp only [mFourier, Pi.zero_apply, fourier_zero, Finset.prod_const_one, ContinuousMap.coe_mk,
    ContinuousMap.one_apply]

lemma mFourier_norm : ‖mFourier n‖ = 1 := by
  apply le_antisymm
  · refine (ContinuousMap.norm_le _ zero_le_one).mpr fun i ↦ ?_
    simp only [mFourier, fourier_apply, ContinuousMap.coe_mk, norm_prod, Circle.norm_coe,
      Finset.prod_const_one, le_rfl]
  · refine (le_of_eq ?_).trans ((mFourier n).norm_coe_le_norm fun _ ↦ 0)
    simp only [mFourier, ContinuousMap.coe_mk, fourier_eval_zero, Finset.prod_const_one,
      CStarRing.norm_one]

lemma mFourier_single [DecidableEq d] (z : d → AddCircle (1 : ℝ)) (i : d) :
    mFourier (Pi.single i 1) z = fourier 1 (z i) := by
  simp_rw [mFourier, ContinuousMap.coe_mk]
  have := Finset.prod_mul_prod_compl {i} (fun j ↦ fourier ((Pi.single i (1 : ℤ) : d → ℤ) j) (z j))
  rw [Finset.prod_singleton, Finset.prod_congr rfl (fun j hj ↦ ?_)] at this
  · rw [← this, Finset.prod_const_one, mul_one, Pi.single_eq_same]
  · rw [Finset.mem_compl, Finset.mem_singleton] at hj
    simp only [Pi.single_eq_of_ne hj, fourier_zero]

end Monomials

section Algebra

def mFourierSubalgebra (d : Type*) [Fintype d] : StarSubalgebra ℂ C(UnitAddTorus d, ℂ) where
  toSubalgebra := Algebra.adjoin ℂ (range mFourier)
  star_mem' := by
    change Algebra.adjoin ℂ (range mFourier) ≤ star (Algebra.adjoin ℂ (range mFourier))
    refine adjoin_le ?_
    rintro _ ⟨n, rfl⟩
    refine subset_adjoin ⟨-n, ?_⟩
    ext1 x
    simp only [mFourier_neg, starRingEnd_apply, ContinuousMap.star_apply]

theorem mFourierSubalgebra_coe :
    (mFourierSubalgebra d).toSubalgebra.toSubmodule = span ℂ (range mFourier) := by
  apply adjoin_eq_span_of_subset
  refine .trans (fun x ↦ Submonoid.closure_induction (fun _ ↦ id) ⟨0, ?_⟩ ?_) subset_span
  · ext z
    simp only [mFourier, Pi.zero_apply, fourier_zero, Finset.prod_const, one_pow,
      ContinuousMap.coe_mk, ContinuousMap.one_apply]
  · rintro _ _ _ _ ⟨m, rfl⟩ ⟨n, rfl⟩
    refine ⟨m + n, ?_⟩
    ext z
    simp only [mFourier, Pi.add_apply, fourier_apply, fourier_add', Finset.prod_mul_distrib,
      ContinuousMap.coe_mk, ContinuousMap.mul_apply]

theorem mFourierSubalgebra_separatesPoints : (mFourierSubalgebra d).SeparatesPoints := by
  classical
  intro x y hxy
  rw [Ne, funext_iff, not_forall] at hxy
  obtain ⟨i, hi⟩ := hxy
  refine ⟨_, ⟨mFourier (Pi.single i 1), subset_adjoin ⟨Pi.single i 1, rfl⟩, rfl⟩, ?_⟩
  dsimp only
  rw [mFourier_single, mFourier_single, fourier_one, fourier_one, Ne, Subtype.coe_inj]
  contrapose hi
  exact AddCircle.injective_toCircle one_ne_zero hi

theorem mFourierSubalgebra_closure_eq_top : (mFourierSubalgebra d).topologicalClosure = ⊤ :=
  ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _
    mFourierSubalgebra_separatesPoints

theorem span_mFourier_closure_eq_top :
    (span ℂ (range <| mFourier (d := d))).topologicalClosure = ⊤ := by
  rw [← mFourierSubalgebra_coe]
  exact congr_arg (Subalgebra.toSubmodule <| StarSubalgebra.toSubalgebra ·)
    mFourierSubalgebra_closure_eq_top

end Algebra

section Integral

variable (a : d → ℝ) {ι : Type*} (b : ι → ℝ)

def measurableEquivPiIoc : UnitAddTorus ι ≃ᵐ {x : ι → ℝ // ∀ i, x i ∈ Ioc (b i) (b i + 1)} :=
  (MeasurableEquiv.piCongrRight fun i => AddCircle.measurableEquivIoc 1 (b i)).trans <|
  MeasurableEquiv.subtypePiEquivPi.symm
