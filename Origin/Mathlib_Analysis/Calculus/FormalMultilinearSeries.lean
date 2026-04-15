/-
Extracted from Analysis/Calculus/FormalMultilinearSeries.lean
Genuine: 26 | Conflates: 2 | Dissolved: 8 | Infrastructure: 14
-/
import Origin.Core
import Mathlib.Analysis.NormedSpace.Multilinear.Curry

/-!
# Formal multilinear series

In this file we define `FormalMultilinearSeries 𝕜 E F` to be a family of `n`-multilinear maps for
all `n`, designed to model the sequence of derivatives of a function. In other files we use this
notion to define `C^n` functions (called `contDiff` in `mathlib`) and analytic functions.

## Notations

We use the notation `E [×n]→L[𝕜] F` for the space of continuous multilinear maps on `E^n` with
values in `F`. This is the space in which the `n`-th derivative of a function from `E` to `F` lives.

## Tags

multilinear, formal series
-/

noncomputable section

open Set Fin Topology

universe u u' v w x

variable {𝕜 : Type u} {𝕜' : Type u'} {E : Type v} {F : Type w} {G : Type x}

section

variable [Ring 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [TopologicalAddGroup E]
  [ContinuousConstSMul 𝕜 E] [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
  [TopologicalAddGroup F] [ContinuousConstSMul 𝕜 F] [AddCommGroup G] [Module 𝕜 G]
  [TopologicalSpace G] [TopologicalAddGroup G] [ContinuousConstSMul 𝕜 G]

@[nolint unusedArguments]
def FormalMultilinearSeries (𝕜 : Type*) (E : Type*) (F : Type*) [Ring 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [TopologicalSpace E] [TopologicalAddGroup E] [ContinuousConstSMul 𝕜 E]
    [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [TopologicalAddGroup F]
    [ContinuousConstSMul 𝕜 F] :=
  ∀ n : ℕ, E[×n]→L[𝕜] F

instance : AddCommGroup (FormalMultilinearSeries 𝕜 E F) :=
  inferInstanceAs <| AddCommGroup <| ∀ n : ℕ, E[×n]→L[𝕜] F

instance : Inhabited (FormalMultilinearSeries 𝕜 E F) :=
  ⟨0⟩

section Module

instance (𝕜') [Semiring 𝕜'] [Module 𝕜' F] [ContinuousConstSMul 𝕜' F] [SMulCommClass 𝕜 𝕜' F] :
    Module 𝕜' (FormalMultilinearSeries 𝕜 E F) :=
  inferInstanceAs <| Module 𝕜' <| ∀ n : ℕ, E[×n]→L[𝕜] F

end Module

namespace FormalMultilinearSeries

@[simp, nolint simpNF]
theorem zero_apply (n : ℕ) : (0 : FormalMultilinearSeries 𝕜 E F) n = 0 := rfl

@[simp]
theorem neg_apply (f : FormalMultilinearSeries 𝕜 E F) (n : ℕ) : (-f) n = - f n := rfl

@[ext]
protected theorem ext {p q : FormalMultilinearSeries 𝕜 E F} (h : ∀ n, p n = q n) : p = q :=
  funext h

protected theorem ne_iff {p q : FormalMultilinearSeries 𝕜 E F} : p ≠ q ↔ ∃ n, p n ≠ q n :=
  Function.ne_iff

def prod (p : FormalMultilinearSeries 𝕜 E F) (q : FormalMultilinearSeries 𝕜 E G) :
    FormalMultilinearSeries 𝕜 E (F × G)
  | n => (p n).prod (q n)

@[simp] def pi {ι : Type*} {F : ι → Type*}
    [∀ i, AddCommGroup (F i)] [∀ i, Module 𝕜 (F i)] [∀ i, TopologicalSpace (F i)]
    [∀ i, TopologicalAddGroup (F i)] [∀ i, ContinuousConstSMul 𝕜 (F i)]
    (p : Π i, FormalMultilinearSeries 𝕜 E (F i)) :
    FormalMultilinearSeries 𝕜 E (Π i, F i)
  | n => ContinuousMultilinearMap.pi (fun i ↦ p i n)

def removeZero (p : FormalMultilinearSeries 𝕜 E F) : FormalMultilinearSeries 𝕜 E F
  | 0 => 0
  | n + 1 => p (n + 1)

@[simp]
theorem removeZero_coeff_zero (p : FormalMultilinearSeries 𝕜 E F) : p.removeZero 0 = 0 :=
  rfl

@[simp]
theorem removeZero_coeff_succ (p : FormalMultilinearSeries 𝕜 E F) (n : ℕ) :
    p.removeZero (n + 1) = p (n + 1) :=
  rfl

theorem removeZero_of_pos (p : FormalMultilinearSeries 𝕜 E F) {n : ℕ} (h : 0 < n) :
    p.removeZero n = p n := by
  rw [← Nat.succ_pred_eq_of_pos h]
  rfl

theorem congr (p : FormalMultilinearSeries 𝕜 E F) {m n : ℕ} {v : Fin m → E} {w : Fin n → E}
    (h1 : m = n) (h2 : ∀ (i : ℕ) (him : i < m) (hin : i < n), v ⟨i, him⟩ = w ⟨i, hin⟩) :
    p m v = p n w := by
  subst n
  congr with ⟨i, hi⟩
  exact h2 i hi hi

def compContinuousLinearMap (p : FormalMultilinearSeries 𝕜 F G) (u : E →L[𝕜] F) :
    FormalMultilinearSeries 𝕜 E G := fun n => (p n).compContinuousLinearMap fun _ : Fin n => u

@[simp]
theorem compContinuousLinearMap_apply (p : FormalMultilinearSeries 𝕜 F G) (u : E →L[𝕜] F) (n : ℕ)
    (v : Fin n → E) : (p.compContinuousLinearMap u) n v = p n (u ∘ v) :=
  rfl

variable (𝕜) [Ring 𝕜'] [SMul 𝕜 𝕜']

variable [Module 𝕜' E] [ContinuousConstSMul 𝕜' E] [IsScalarTower 𝕜 𝕜' E]

variable [Module 𝕜' F] [ContinuousConstSMul 𝕜' F] [IsScalarTower 𝕜 𝕜' F]

@[simp]
protected def restrictScalars (p : FormalMultilinearSeries 𝕜' E F) :
    FormalMultilinearSeries 𝕜 E F := fun n => (p n).restrictScalars 𝕜

end FormalMultilinearSeries

end

namespace FormalMultilinearSeries

variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F]

variable (p : FormalMultilinearSeries 𝕜 E F)

def shift : FormalMultilinearSeries 𝕜 E (E →L[𝕜] F) := fun n => (p n.succ).curryRight

def unshift (q : FormalMultilinearSeries 𝕜 E (E →L[𝕜] F)) (z : F) : FormalMultilinearSeries 𝕜 E F
  | 0 => (continuousMultilinearCurryFin0 𝕜 E F).symm z
  | n + 1 => (continuousMultilinearCurryRightEquiv' 𝕜 n E F).symm (q n)

end FormalMultilinearSeries

section

variable [Ring 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [TopologicalAddGroup E]
  [ContinuousConstSMul 𝕜 E] [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
  [TopologicalAddGroup F] [ContinuousConstSMul 𝕜 F] [AddCommGroup G] [Module 𝕜 G]
  [TopologicalSpace G] [TopologicalAddGroup G] [ContinuousConstSMul 𝕜 G]

namespace ContinuousLinearMap

def compFormalMultilinearSeries (f : F →L[𝕜] G) (p : FormalMultilinearSeries 𝕜 E F) :
    FormalMultilinearSeries 𝕜 E G := fun n => f.compContinuousMultilinearMap (p n)

@[simp]
theorem compFormalMultilinearSeries_apply (f : F →L[𝕜] G) (p : FormalMultilinearSeries 𝕜 E F)
    (n : ℕ) : (f.compFormalMultilinearSeries p) n = f.compContinuousMultilinearMap (p n) :=
  rfl

theorem compFormalMultilinearSeries_apply' (f : F →L[𝕜] G) (p : FormalMultilinearSeries 𝕜 E F)
    (n : ℕ) (v : Fin n → E) : (f.compFormalMultilinearSeries p) n v = f (p n v) :=
  rfl

end ContinuousLinearMap

namespace ContinuousMultilinearMap

variable {ι : Type*} {E : ι → Type*} [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)]
  [∀ i, TopologicalSpace (E i)] [∀ i, TopologicalAddGroup (E i)]
  [∀ i, ContinuousConstSMul 𝕜 (E i)] [Fintype ι] (f : ContinuousMultilinearMap 𝕜 E F)

noncomputable def toFormalMultilinearSeries : FormalMultilinearSeries 𝕜 (∀ i, E i) F :=
  fun n ↦ if h : Fintype.card ι = n then
    (f.compContinuousLinearMap .proj).domDomCongr (Fintype.equivFinOfCardEq h)
  else 0

end ContinuousMultilinearMap

end

namespace FormalMultilinearSeries

section Order

variable [Ring 𝕜] {n : ℕ} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [TopologicalAddGroup E] [ContinuousConstSMul 𝕜 E] [AddCommGroup F] [Module 𝕜 F]
  [TopologicalSpace F] [TopologicalAddGroup F] [ContinuousConstSMul 𝕜 F]
  {p : FormalMultilinearSeries 𝕜 E F}

noncomputable def order (p : FormalMultilinearSeries 𝕜 E F) : ℕ :=
  sInf { n | p n ≠ 0 }

@[simp]
theorem order_zero : (0 : FormalMultilinearSeries 𝕜 E F).order = 0 := by simp [order]

-- DISSOLVED: ne_zero_of_order_ne_zero

-- DISSOLVED: order_eq_find

-- DISSOLVED: order_eq_find'

-- DISSOLVED: order_eq_zero_iff'

-- DISSOLVED: order_eq_zero_iff

-- DISSOLVED: apply_order_ne_zero

-- DISSOLVED: apply_order_ne_zero'

theorem apply_eq_zero_of_lt_order (hp : n < p.order) : p n = 0 :=
  by_contra <| Nat.not_mem_of_lt_sInf hp

end Order

section Coef

variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {p : FormalMultilinearSeries 𝕜 𝕜 E} {f : 𝕜 → E} {n : ℕ} {z : 𝕜} {y : Fin n → 𝕜}

def coeff (p : FormalMultilinearSeries 𝕜 𝕜 E) (n : ℕ) : E :=
  p n 1

theorem mkPiRing_coeff_eq (p : FormalMultilinearSeries 𝕜 𝕜 E) (n : ℕ) :
    ContinuousMultilinearMap.mkPiRing 𝕜 (Fin n) (p.coeff n) = p n :=
  (p n).mkPiRing_apply_one_eq_self

@[simp]
theorem apply_eq_prod_smul_coeff : p n y = (∏ i, y i) • p.coeff n := by
  convert (p n).toMultilinearMap.map_smul_univ y 1
  simp only [Pi.one_apply, Algebra.id.smul_eq_mul, mul_one]

theorem coeff_eq_zero : p.coeff n = 0 ↔ p n = 0 := by
  rw [← mkPiRing_coeff_eq p, ContinuousMultilinearMap.mkPiRing_eq_zero_iff]

theorem apply_eq_pow_smul_coeff : (p n fun _ => z) = z ^ n • p.coeff n := by simp

@[simp]
theorem norm_apply_eq_norm_coef : ‖p n‖ = ‖coeff p n‖ := by
  rw [← mkPiRing_coeff_eq p, ContinuousMultilinearMap.norm_mkPiRing]

end Coef

section Fslope

variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {p : FormalMultilinearSeries 𝕜 𝕜 E} {n : ℕ}

noncomputable def fslope (p : FormalMultilinearSeries 𝕜 𝕜 E) : FormalMultilinearSeries 𝕜 𝕜 E :=
  fun n => (p (n + 1)).curryLeft 1

@[simp]
theorem coeff_fslope : p.fslope.coeff n = p.coeff (n + 1) := by
  simp only [fslope, coeff, ContinuousMultilinearMap.curryLeft_apply]
  congr 1
  exact Fin.cons_self_tail (fun _ => (1 : 𝕜))

@[simp]
theorem coeff_iterate_fslope (k n : ℕ) : (fslope^[k] p).coeff n = p.coeff (n + k) := by
  induction k generalizing p with
  | zero => rfl
  | succ k ih => simp [ih, add_assoc]

end Fslope

end FormalMultilinearSeries

section Const

-- CONFLATES (assumes ground = zero): constFormalMultilinearSeries
def constFormalMultilinearSeries (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : Type*)
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [ContinuousConstSMul 𝕜 E] [TopologicalAddGroup E]
    {F : Type*} [NormedAddCommGroup F] [TopologicalAddGroup F] [NormedSpace 𝕜 F]
    [ContinuousConstSMul 𝕜 F] (c : F) : FormalMultilinearSeries 𝕜 E F
  | 0 => ContinuousMultilinearMap.uncurry0 _ _ c
  | _ => 0

-- DISSOLVED: constFormalMultilinearSeries_apply

-- CONFLATES (assumes ground = zero): constFormalMultilinearSeries_zero
@[simp]
lemma constFormalMultilinearSeries_zero [NontriviallyNormedField 𝕜] [NormedAddCommGroup E ]
    [NormedAddCommGroup F] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] :
    constFormalMultilinearSeries 𝕜 E (0 : F) = 0 := by
  ext n x
  simp only [FormalMultilinearSeries.zero_apply, ContinuousMultilinearMap.zero_apply,
    constFormalMultilinearSeries]
  induction n
  · simp only [ContinuousMultilinearMap.uncurry0_apply]
  · simp only [constFormalMultilinearSeries.match_1.eq_2, ContinuousMultilinearMap.zero_apply]

end Const

section Linear

variable [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

namespace ContinuousLinearMap

def fpowerSeries (f : E →L[𝕜] F) (x : E) : FormalMultilinearSeries 𝕜 E F
  | 0 => ContinuousMultilinearMap.uncurry0 𝕜 _ (f x)
  | 1 => (continuousMultilinearCurryFin1 𝕜 E F).symm f
  | _ => 0

@[simp]
theorem fpowerSeries_apply_zero (f : E →L[𝕜] F) (x : E) :
    f.fpowerSeries x 0 = ContinuousMultilinearMap.uncurry0 𝕜 _ (f x) :=
  rfl

@[simp]
theorem fpowerSeries_apply_one (f : E →L[𝕜] F) (x : E) :
    f.fpowerSeries x 1 = (continuousMultilinearCurryFin1 𝕜 E F).symm f :=
  rfl

@[simp]
theorem fpowerSeries_apply_add_two (f : E →L[𝕜] F) (x : E) (n : ℕ) : f.fpowerSeries x (n + 2) = 0 :=
  rfl

end ContinuousLinearMap

end Linear
