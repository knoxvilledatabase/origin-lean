/-
Extracted from Topology/Algebra/Module/Basic.lean
Genuine: 224 | Conflates: 1 | Dissolved: 3 | Infrastructure: 162
-/
import Origin.Core
import Mathlib.Algebra.Module.Opposite
import Mathlib.LinearAlgebra.Projection
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.UniformGroup.Defs
import Mathlib.Topology.UniformSpace.UniformEmbedding
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Theory of topological modules and continuous linear maps.

We use the class `ContinuousSMul` for topological (semi) modules and topological vector spaces.

In this file we define continuous (semi-)linear maps, as semilinear maps between topological
modules which are continuous. The set of continuous semilinear maps between the topological
`R₁`-module `M` and `R₂`-module `M₂` with respect to the `RingHom` `σ` is denoted by `M →SL[σ] M₂`.
Plain linear maps are denoted by `M →L[R] M₂` and star-linear maps by `M →L⋆[R] M₂`.

The corresponding notation for equivalences is `M ≃SL[σ] M₂`, `M ≃L[R] M₂` and `M ≃L⋆[R] M₂`.
-/

open LinearMap (ker range)

open Topology Filter Pointwise

universe u v w u'

section

variable {R : Type*} {M : Type*} [Ring R] [TopologicalSpace R] [TopologicalSpace M]
  [AddCommGroup M] [Module R M]

theorem ContinuousSMul.of_nhds_zero [TopologicalRing R] [TopologicalAddGroup M]
    (hmul : Tendsto (fun p : R × M => p.1 • p.2) (𝓝 0 ×ˢ 𝓝 0) (𝓝 0))
    (hmulleft : ∀ m : M, Tendsto (fun a : R => a • m) (𝓝 0) (𝓝 0))
    (hmulright : ∀ a : R, Tendsto (fun m : M => a • m) (𝓝 0) (𝓝 0)) : ContinuousSMul R M where
  continuous_smul := by
    rw [← nhds_prod_eq] at hmul
    refine continuous_of_continuousAt_zero₂ (AddMonoidHom.smul : R →+ M →+ M) ?_ ?_ ?_ <;>
      simpa [ContinuousAt]

end

section

variable {R : Type*} {M : Type*} [Ring R] [TopologicalSpace R] [TopologicalSpace M]
  [AddCommGroup M] [ContinuousAdd M] [Module R M] [ContinuousSMul R M]

theorem Submodule.eq_top_of_nonempty_interior' [NeBot (𝓝[{ x : R | IsUnit x }] 0)]
    (s : Submodule R M) (hs : (interior (s : Set M)).Nonempty) : s = ⊤ := by
  rcases hs with ⟨y, hy⟩
  refine Submodule.eq_top_iff'.2 fun x => ?_
  rw [mem_interior_iff_mem_nhds] at hy
  have : Tendsto (fun c : R => y + c • x) (𝓝[{ x : R | IsUnit x }] 0) (𝓝 (y + (0 : R) • x)) :=
    tendsto_const_nhds.add ((tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).smul tendsto_const_nhds)
  rw [zero_smul, add_zero] at this
  obtain ⟨_, hu : y + _ • _ ∈ s, u, rfl⟩ :=
    nonempty_of_mem (inter_mem (Filter.mem_map.1 (this hy)) self_mem_nhdsWithin)
  have hy' : y ∈ ↑s := mem_of_mem_nhds hy
  rwa [s.add_mem_iff_right hy', ← Units.smul_def, s.smul_mem_iff' u] at hu

variable (R M)

-- CONFLATES (assumes ground = zero): Module.punctured_nhds_neBot
theorem Module.punctured_nhds_neBot [Nontrivial M] [NeBot (𝓝[≠] (0 : R))] [NoZeroSMulDivisors R M]
    (x : M) : NeBot (𝓝[≠] x) := by
  rcases exists_ne (0 : M) with ⟨y, hy⟩
  suffices Tendsto (fun c : R => x + c • y) (𝓝[≠] 0) (𝓝[≠] x) from this.neBot
  refine Tendsto.inf ?_ (tendsto_principal_principal.2 <| ?_)
  · convert tendsto_const_nhds.add ((@tendsto_id R _).smul_const y)
    rw [zero_smul, add_zero]
  · intro c hc
    simpa [hy] using hc

end

section LatticeOps

variable {R M₁ M₂ : Type*} [SMul R M₁] [SMul R M₂] [u : TopologicalSpace R]
  {t : TopologicalSpace M₂} [ContinuousSMul R M₂]
  {F : Type*} [FunLike F M₁ M₂] [MulActionHomClass F R M₁ M₂] (f : F)

theorem continuousSMul_induced : @ContinuousSMul R M₁ _ u (t.induced f) :=
  let _ : TopologicalSpace M₁ := t.induced f
  IsInducing.continuousSMul ⟨rfl⟩ continuous_id (map_smul f _ _)

end LatticeOps

lemma TopologicalSpace.IsSeparable.span {R M : Type*} [AddCommMonoid M] [Semiring R] [Module R M]
    [TopologicalSpace M] [TopologicalSpace R] [SeparableSpace R]
    [ContinuousAdd M] [ContinuousSMul R M] {s : Set M} (hs : IsSeparable s) :
    IsSeparable (Submodule.span R s : Set M) := by
  rw [span_eq_iUnion_nat]
  refine .iUnion fun n ↦ .image ?_ ?_
  · have : IsSeparable {f : Fin n → R × M | ∀ (i : Fin n), f i ∈ Set.univ ×ˢ s} := by
      apply isSeparable_pi (fun i ↦ .prod (.of_separableSpace Set.univ) hs)
    rwa [Set.univ_prod] at this
  · apply continuous_finset_sum _ (fun i _ ↦ ?_)
    exact (continuous_fst.comp (continuous_apply i)).smul (continuous_snd.comp (continuous_apply i))

namespace Submodule

variable {α β : Type*} [TopologicalSpace β]

instance topologicalAddGroup [Ring α] [AddCommGroup β] [Module α β] [TopologicalAddGroup β]
    (S : Submodule α β) : TopologicalAddGroup S :=
  inferInstanceAs (TopologicalAddGroup S.toAddSubgroup)

end Submodule

section closure

variable {R : Type u} {M : Type v} [Semiring R] [TopologicalSpace M] [AddCommMonoid M] [Module R M]
  [ContinuousConstSMul R M]

theorem Submodule.mapsTo_smul_closure (s : Submodule R M) (c : R) :
    Set.MapsTo (c • ·) (closure s : Set M) (closure s) :=
  have : Set.MapsTo (c • ·) (s : Set M) s := fun _ h ↦ s.smul_mem c h
  this.closure (continuous_const_smul c)

theorem Submodule.smul_closure_subset (s : Submodule R M) (c : R) :
    c • closure (s : Set M) ⊆ closure (s : Set M) :=
  (s.mapsTo_smul_closure c).image_subset

variable [ContinuousAdd M]

def Submodule.topologicalClosure (s : Submodule R M) : Submodule R M :=
  { s.toAddSubmonoid.topologicalClosure with
    smul_mem' := s.mapsTo_smul_closure }

@[simp]
theorem Submodule.topologicalClosure_coe (s : Submodule R M) :
    (s.topologicalClosure : Set M) = closure (s : Set M) :=
  rfl

theorem Submodule.le_topologicalClosure (s : Submodule R M) : s ≤ s.topologicalClosure :=
  subset_closure

theorem Submodule.closure_subset_topologicalClosure_span (s : Set M) :
    closure s ⊆ (span R s).topologicalClosure := by
  rw [Submodule.topologicalClosure_coe]
  exact closure_mono subset_span

theorem Submodule.isClosed_topologicalClosure (s : Submodule R M) :
    IsClosed (s.topologicalClosure : Set M) := isClosed_closure

theorem Submodule.topologicalClosure_minimal (s : Submodule R M) {t : Submodule R M} (h : s ≤ t)
    (ht : IsClosed (t : Set M)) : s.topologicalClosure ≤ t :=
  closure_minimal h ht

theorem Submodule.topologicalClosure_mono {s : Submodule R M} {t : Submodule R M} (h : s ≤ t) :
    s.topologicalClosure ≤ t.topologicalClosure :=
  closure_mono h

theorem IsClosed.submodule_topologicalClosure_eq {s : Submodule R M} (hs : IsClosed (s : Set M)) :
    s.topologicalClosure = s :=
  SetLike.ext' hs.closure_eq

theorem Submodule.dense_iff_topologicalClosure_eq_top {s : Submodule R M} :
    Dense (s : Set M) ↔ s.topologicalClosure = ⊤ := by
  rw [← SetLike.coe_set_eq, dense_iff_closure_eq]
  simp

instance Submodule.topologicalClosure.completeSpace {M' : Type*} [AddCommMonoid M'] [Module R M']
    [UniformSpace M'] [ContinuousAdd M'] [ContinuousConstSMul R M'] [CompleteSpace M']
    (U : Submodule R M') : CompleteSpace U.topologicalClosure :=
  isClosed_closure.completeSpace_coe

theorem Submodule.isClosed_or_dense_of_isCoatom (s : Submodule R M) (hs : IsCoatom s) :
    IsClosed (s : Set M) ∨ Dense (s : Set M) := by
  refine (hs.le_iff.mp s.le_topologicalClosure).symm.imp ?_ dense_iff_topologicalClosure_eq_top.mpr
  exact fun h ↦ h ▸ isClosed_closure

end closure

section Pi

theorem LinearMap.continuous_on_pi {ι : Type*} {R : Type*} {M : Type*} [Finite ι] [Semiring R]
    [TopologicalSpace R] [AddCommMonoid M] [Module R M] [TopologicalSpace M] [ContinuousAdd M]
    [ContinuousSMul R M] (f : (ι → R) →ₗ[R] M) : Continuous f := by
  cases nonempty_fintype ι
  classical
    -- for the proof, write `f` in the standard basis, and use that each coordinate is a continuous
    -- function.
    have : (f : (ι → R) → M) = fun x => ∑ i : ι, x i • f fun j => if i = j then 1 else 0 := by
      ext x
      exact f.pi_apply_eq_sum_univ x
    rw [this]
    refine continuous_finset_sum _ fun i _ => ?_
    exact (continuous_apply i).smul continuous_const

end Pi

structure ContinuousLinearMap {R : Type*} {S : Type*} [Semiring R] [Semiring S] (σ : R →+* S)
    (M : Type*) [TopologicalSpace M] [AddCommMonoid M] (M₂ : Type*) [TopologicalSpace M₂]
    [AddCommMonoid M₂] [Module R M] [Module S M₂] extends M →ₛₗ[σ] M₂ where
  cont : Continuous toFun := by continuity

attribute [inherit_doc ContinuousLinearMap] ContinuousLinearMap.cont

notation:25 M " →SL[" σ "] " M₂ => ContinuousLinearMap σ M M₂

notation:25 M " →L[" R "] " M₂ => ContinuousLinearMap (RingHom.id R) M M₂

class ContinuousSemilinearMapClass (F : Type*) {R S : outParam Type*} [Semiring R] [Semiring S]
    (σ : outParam <| R →+* S) (M : outParam Type*) [TopologicalSpace M] [AddCommMonoid M]
    (M₂ : outParam Type*) [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M]
    [Module S M₂] [FunLike F M M₂]
    extends SemilinearMapClass F σ M M₂, ContinuousMapClass F M M₂ : Prop

abbrev ContinuousLinearMapClass (F : Type*) (R : outParam Type*) [Semiring R]
    (M : outParam Type*) [TopologicalSpace M] [AddCommMonoid M] (M₂ : outParam Type*)
    [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M] [Module R M₂] [FunLike F M M₂] :=
  ContinuousSemilinearMapClass F (RingHom.id R) M M₂

structure ContinuousLinearEquiv {R : Type*} {S : Type*} [Semiring R] [Semiring S] (σ : R →+* S)
    {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (M : Type*) [TopologicalSpace M]
    [AddCommMonoid M] (M₂ : Type*) [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M]
    [Module S M₂] extends M ≃ₛₗ[σ] M₂ where
  continuous_toFun : Continuous toFun := by continuity
  continuous_invFun : Continuous invFun := by continuity

attribute [inherit_doc ContinuousLinearEquiv] ContinuousLinearEquiv.continuous_toFun

ContinuousLinearEquiv.continuous_invFun

notation:50 M " ≃SL[" σ "] " M₂ => ContinuousLinearEquiv σ M M₂

notation:50 M " ≃L[" R "] " M₂ => ContinuousLinearEquiv (RingHom.id R) M M₂

class ContinuousSemilinearEquivClass (F : Type*) {R : outParam Type*} {S : outParam Type*}
    [Semiring R] [Semiring S] (σ : outParam <| R →+* S) {σ' : outParam <| S →+* R}
    [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (M : outParam Type*) [TopologicalSpace M]
    [AddCommMonoid M] (M₂ : outParam Type*) [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M]
    [Module S M₂] [EquivLike F M M₂] extends SemilinearEquivClass F σ M M₂ : Prop where
  map_continuous : ∀ f : F, Continuous f := by continuity
  inv_continuous : ∀ f : F, Continuous (EquivLike.inv f) := by continuity

attribute [inherit_doc ContinuousSemilinearEquivClass]

ContinuousSemilinearEquivClass.map_continuous

ContinuousSemilinearEquivClass.inv_continuous

abbrev ContinuousLinearEquivClass (F : Type*) (R : outParam Type*) [Semiring R]
    (M : outParam Type*) [TopologicalSpace M] [AddCommMonoid M] (M₂ : outParam Type*)
    [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M] [Module R M₂] [EquivLike F M M₂] :=
  ContinuousSemilinearEquivClass F (RingHom.id R) M M₂

namespace ContinuousSemilinearEquivClass

variable (F : Type*) {R : Type*} {S : Type*} [Semiring R] [Semiring S] (σ : R →+* S)
  {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
  (M : Type*) [TopologicalSpace M] [AddCommMonoid M]
  (M₂ : Type*) [TopologicalSpace M₂] [AddCommMonoid M₂]
  [Module R M] [Module S M₂]

instance (priority := 100) continuousSemilinearMapClass [EquivLike F M M₂]
    [s : ContinuousSemilinearEquivClass F σ M M₂] : ContinuousSemilinearMapClass F σ M M₂ :=
  { s with }

end ContinuousSemilinearEquivClass

section PointwiseLimits

variable {M₁ M₂ α R S : Type*} [TopologicalSpace M₂] [T2Space M₂] [Semiring R] [Semiring S]
  [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁] [Module S M₂] [ContinuousConstSMul S M₂]

variable [ContinuousAdd M₂] {σ : R →+* S} {l : Filter α}

@[simps (config := .asFn)]
def linearMapOfMemClosureRangeCoe (f : M₁ → M₂)
    (hf : f ∈ closure (Set.range ((↑) : (M₁ →ₛₗ[σ] M₂) → M₁ → M₂))) : M₁ →ₛₗ[σ] M₂ :=
  { addMonoidHomOfMemClosureRangeCoe f hf with
    map_smul' := (isClosed_setOf_map_smul M₁ M₂ σ).closure_subset_iff.2
      (Set.range_subset_iff.2 LinearMap.map_smulₛₗ) hf }

@[simps! (config := .asFn)]
def linearMapOfTendsto (f : M₁ → M₂) (g : α → M₁ →ₛₗ[σ] M₂) [l.NeBot]
    (h : Tendsto (fun a x => g a x) l (𝓝 f)) : M₁ →ₛₗ[σ] M₂ :=
  linearMapOfMemClosureRangeCoe f <|
    mem_closure_of_tendsto h <| Eventually.of_forall fun _ => Set.mem_range_self _

variable (M₁ M₂ σ)

theorem LinearMap.isClosed_range_coe : IsClosed (Set.range ((↑) : (M₁ →ₛₗ[σ] M₂) → M₁ → M₂)) :=
  isClosed_of_closure_subset fun f hf => ⟨linearMapOfMemClosureRangeCoe f hf, rfl⟩

end PointwiseLimits

namespace ContinuousLinearMap

section Semiring

/-!
### Properties that hold for non-necessarily commutative semirings.
-/

variable {R₁ : Type*} {R₂ : Type*} {R₃ : Type*} [Semiring R₁] [Semiring R₂] [Semiring R₃]
  {σ₁₂ : R₁ →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R₁ →+* R₃} {M₁ : Type*} [TopologicalSpace M₁]
  [AddCommMonoid M₁] {M'₁ : Type*} [TopologicalSpace M'₁] [AddCommMonoid M'₁] {M₂ : Type*}
  [TopologicalSpace M₂] [AddCommMonoid M₂] {M₃ : Type*} [TopologicalSpace M₃] [AddCommMonoid M₃]
  {M₄ : Type*} [TopologicalSpace M₄] [AddCommMonoid M₄] [Module R₁ M₁] [Module R₁ M'₁]
  [Module R₂ M₂] [Module R₃ M₃]

attribute [coe] ContinuousLinearMap.toLinearMap

instance LinearMap.coe : Coe (M₁ →SL[σ₁₂] M₂) (M₁ →ₛₗ[σ₁₂] M₂) := ⟨toLinearMap⟩

theorem coe_injective : Function.Injective ((↑) : (M₁ →SL[σ₁₂] M₂) → M₁ →ₛₗ[σ₁₂] M₂) := by
  intro f g H
  cases f
  cases g
  congr

instance funLike : FunLike (M₁ →SL[σ₁₂] M₂) M₁ M₂ where
  coe f := f.toLinearMap
  coe_injective' _ _ h := coe_injective (DFunLike.coe_injective h)

instance continuousSemilinearMapClass :
    ContinuousSemilinearMapClass (M₁ →SL[σ₁₂] M₂) σ₁₂ M₁ M₂ where
  map_add f := map_add f.toLinearMap
  map_continuous f := f.2
  map_smulₛₗ f := f.toLinearMap.map_smul'

theorem coe_mk (f : M₁ →ₛₗ[σ₁₂] M₂) (h) : (mk f h : M₁ →ₛₗ[σ₁₂] M₂) = f :=
  rfl

@[simp]
theorem coe_mk' (f : M₁ →ₛₗ[σ₁₂] M₂) (h) : (mk f h : M₁ → M₂) = f :=
  rfl

@[continuity, fun_prop]
protected theorem continuous (f : M₁ →SL[σ₁₂] M₂) : Continuous f :=
  f.2

protected theorem uniformContinuous {E₁ E₂ : Type*} [UniformSpace E₁] [UniformSpace E₂]
    [AddCommGroup E₁] [AddCommGroup E₂] [Module R₁ E₁] [Module R₂ E₂] [UniformAddGroup E₁]
    [UniformAddGroup E₂] (f : E₁ →SL[σ₁₂] E₂) : UniformContinuous f :=
  uniformContinuous_addMonoidHom_of_continuous f.continuous

@[simp, norm_cast]
theorem coe_inj {f g : M₁ →SL[σ₁₂] M₂} : (f : M₁ →ₛₗ[σ₁₂] M₂) = g ↔ f = g :=
  coe_injective.eq_iff

theorem coeFn_injective : @Function.Injective (M₁ →SL[σ₁₂] M₂) (M₁ → M₂) (↑) :=
  DFunLike.coe_injective

def Simps.apply (h : M₁ →SL[σ₁₂] M₂) : M₁ → M₂ :=
  h

def Simps.coe (h : M₁ →SL[σ₁₂] M₂) : M₁ →ₛₗ[σ₁₂] M₂ :=
  h

initialize_simps_projections ContinuousLinearMap (toLinearMap_toFun → apply, toLinearMap → coe)

@[ext]
theorem ext {f g : M₁ →SL[σ₁₂] M₂} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

protected def copy (f : M₁ →SL[σ₁₂] M₂) (f' : M₁ → M₂) (h : f' = ⇑f) : M₁ →SL[σ₁₂] M₂ where
  toLinearMap := f.toLinearMap.copy f' h
  cont := show Continuous f' from h.symm ▸ f.continuous

@[simp]
theorem coe_copy (f : M₁ →SL[σ₁₂] M₂) (f' : M₁ → M₂) (h : f' = ⇑f) : ⇑(f.copy f' h) = f' :=
  rfl

theorem copy_eq (f : M₁ →SL[σ₁₂] M₂) (f' : M₁ → M₂) (h : f' = ⇑f) : f.copy f' h = f :=
  DFunLike.ext' h

theorem range_coeFn_eq :
    Set.range ((⇑) : (M₁ →SL[σ₁₂] M₂) → (M₁ → M₂)) =
      {f | Continuous f} ∩ Set.range ((⇑) : (M₁ →ₛₗ[σ₁₂] M₂) → (M₁ → M₂)) := by
  ext f
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨f.continuous, f, rfl⟩
  · rintro ⟨hfc, f, rfl⟩
    exact ⟨⟨f, hfc⟩, rfl⟩

protected theorem map_zero (f : M₁ →SL[σ₁₂] M₂) : f (0 : M₁) = 0 :=
  map_zero f

protected theorem map_add (f : M₁ →SL[σ₁₂] M₂) (x y : M₁) : f (x + y) = f x + f y :=
  map_add f x y

@[simp]
protected theorem map_smulₛₗ (f : M₁ →SL[σ₁₂] M₂) (c : R₁) (x : M₁) : f (c • x) = σ₁₂ c • f x :=
  (toLinearMap _).map_smulₛₗ _ _

protected theorem map_smul [Module R₁ M₂] (f : M₁ →L[R₁] M₂) (c : R₁) (x : M₁) :
    f (c • x) = c • f x := by simp only [RingHom.id_apply, ContinuousLinearMap.map_smulₛₗ]

@[simp]
theorem map_smul_of_tower {R S : Type*} [Semiring S] [SMul R M₁] [Module S M₁] [SMul R M₂]
    [Module S M₂] [LinearMap.CompatibleSMul M₁ M₂ R S] (f : M₁ →L[S] M₂) (c : R) (x : M₁) :
    f (c • x) = c • f x :=
  LinearMap.CompatibleSMul.map_smul (f : M₁ →ₗ[S] M₂) c x

@[simp, norm_cast]
theorem coe_coe (f : M₁ →SL[σ₁₂] M₂) : ⇑(f : M₁ →ₛₗ[σ₁₂] M₂) = f :=
  rfl

@[ext]
theorem ext_ring [TopologicalSpace R₁] {f g : R₁ →L[R₁] M₁} (h : f 1 = g 1) : f = g :=
  coe_inj.1 <| LinearMap.ext_ring h

theorem eqOn_closure_span [T2Space M₂] {s : Set M₁} {f g : M₁ →SL[σ₁₂] M₂} (h : Set.EqOn f g s) :
    Set.EqOn f g (closure (Submodule.span R₁ s : Set M₁)) :=
  (LinearMap.eqOn_span' h).closure f.continuous g.continuous

theorem ext_on [T2Space M₂] {s : Set M₁} (hs : Dense (Submodule.span R₁ s : Set M₁))
    {f g : M₁ →SL[σ₁₂] M₂} (h : Set.EqOn f g s) : f = g :=
  ext fun x => eqOn_closure_span h (hs x)

theorem _root_.Submodule.topologicalClosure_map [RingHomSurjective σ₁₂] [TopologicalSpace R₁]
    [TopologicalSpace R₂] [ContinuousSMul R₁ M₁] [ContinuousAdd M₁] [ContinuousSMul R₂ M₂]
    [ContinuousAdd M₂] (f : M₁ →SL[σ₁₂] M₂) (s : Submodule R₁ M₁) :
    s.topologicalClosure.map (f : M₁ →ₛₗ[σ₁₂] M₂) ≤
      (s.map (f : M₁ →ₛₗ[σ₁₂] M₂)).topologicalClosure :=
  image_closure_subset_closure_image f.continuous

theorem _root_.DenseRange.topologicalClosure_map_submodule [RingHomSurjective σ₁₂]
    [TopologicalSpace R₁] [TopologicalSpace R₂] [ContinuousSMul R₁ M₁] [ContinuousAdd M₁]
    [ContinuousSMul R₂ M₂] [ContinuousAdd M₂] {f : M₁ →SL[σ₁₂] M₂} (hf' : DenseRange f)
    {s : Submodule R₁ M₁} (hs : s.topologicalClosure = ⊤) :
    (s.map (f : M₁ →ₛₗ[σ₁₂] M₂)).topologicalClosure = ⊤ := by
  rw [SetLike.ext'_iff] at hs ⊢
  simp only [Submodule.topologicalClosure_coe, Submodule.top_coe, ← dense_iff_closure_eq] at hs ⊢
  exact hf'.dense_image f.continuous hs

section SMulMonoid

variable {S₂ T₂ : Type*} [Monoid S₂] [Monoid T₂]

variable [DistribMulAction S₂ M₂] [SMulCommClass R₂ S₂ M₂] [ContinuousConstSMul S₂ M₂]

variable [DistribMulAction T₂ M₂] [SMulCommClass R₂ T₂ M₂] [ContinuousConstSMul T₂ M₂]

instance instSMul : SMul S₂ (M₁ →SL[σ₁₂] M₂) where
  smul c f := ⟨c • (f : M₁ →ₛₗ[σ₁₂] M₂), (f.2.const_smul _ : Continuous fun x => c • f x)⟩

instance mulAction : MulAction S₂ (M₁ →SL[σ₁₂] M₂) where
  one_smul _f := ext fun _x => one_smul _ _
  mul_smul _a _b _f := ext fun _x => mul_smul _ _ _

theorem smul_apply (c : S₂) (f : M₁ →SL[σ₁₂] M₂) (x : M₁) : (c • f) x = c • f x :=
  rfl

@[simp, norm_cast]
theorem coe_smul (c : S₂) (f : M₁ →SL[σ₁₂] M₂) :
    ↑(c • f) = c • (f : M₁ →ₛₗ[σ₁₂] M₂) :=
  rfl

@[simp, norm_cast]
theorem coe_smul' (c : S₂) (f : M₁ →SL[σ₁₂] M₂) :
    ↑(c • f) = c • (f : M₁ → M₂) :=
  rfl

instance isScalarTower [SMul S₂ T₂] [IsScalarTower S₂ T₂ M₂] :
    IsScalarTower S₂ T₂ (M₁ →SL[σ₁₂] M₂) :=
  ⟨fun a b f => ext fun x => smul_assoc a b (f x)⟩

instance smulCommClass [SMulCommClass S₂ T₂ M₂] : SMulCommClass S₂ T₂ (M₁ →SL[σ₁₂] M₂) :=
  ⟨fun a b f => ext fun x => smul_comm a b (f x)⟩

end SMulMonoid

instance zero : Zero (M₁ →SL[σ₁₂] M₂) :=
  ⟨⟨0, continuous_zero⟩⟩

instance inhabited : Inhabited (M₁ →SL[σ₁₂] M₂) :=
  ⟨0⟩

@[simp]
theorem default_def : (default : M₁ →SL[σ₁₂] M₂) = 0 :=
  rfl

@[simp]
theorem zero_apply (x : M₁) : (0 : M₁ →SL[σ₁₂] M₂) x = 0 :=
  rfl

@[simp, norm_cast]
theorem coe_zero : ((0 : M₁ →SL[σ₁₂] M₂) : M₁ →ₛₗ[σ₁₂] M₂) = 0 :=
  rfl

@[norm_cast]
theorem coe_zero' : ⇑(0 : M₁ →SL[σ₁₂] M₂) = 0 :=
  rfl

instance uniqueOfLeft [Subsingleton M₁] : Unique (M₁ →SL[σ₁₂] M₂) :=
  coe_injective.unique

instance uniqueOfRight [Subsingleton M₂] : Unique (M₁ →SL[σ₁₂] M₂) :=
  coe_injective.unique

-- DISSOLVED: exists_ne_zero

section

variable (R₁ M₁)

def id : M₁ →L[R₁] M₁ :=
  ⟨LinearMap.id, continuous_id⟩

end

instance one : One (M₁ →L[R₁] M₁) :=
  ⟨id R₁ M₁⟩

theorem one_def : (1 : M₁ →L[R₁] M₁) = id R₁ M₁ :=
  rfl

theorem id_apply (x : M₁) : id R₁ M₁ x = x :=
  rfl

@[simp, norm_cast]
theorem coe_id : (id R₁ M₁ : M₁ →ₗ[R₁] M₁) = LinearMap.id :=
  rfl

@[simp, norm_cast]
theorem coe_id' : ⇑(id R₁ M₁) = _root_.id :=
  rfl

@[simp, norm_cast]
theorem coe_eq_id {f : M₁ →L[R₁] M₁} : (f : M₁ →ₗ[R₁] M₁) = LinearMap.id ↔ f = id _ _ := by
  rw [← coe_id, coe_inj]

@[simp]
theorem one_apply (x : M₁) : (1 : M₁ →L[R₁] M₁) x = x :=
  rfl

instance [Nontrivial M₁] : Nontrivial (M₁ →L[R₁] M₁) :=
  ⟨0, 1, fun e ↦
    have ⟨x, hx⟩ := exists_ne (0 : M₁); hx (by simpa using DFunLike.congr_fun e.symm x)⟩

section Add

variable [ContinuousAdd M₂]

instance add : Add (M₁ →SL[σ₁₂] M₂) :=
  ⟨fun f g => ⟨f + g, f.2.add g.2⟩⟩

@[simp]
theorem add_apply (f g : M₁ →SL[σ₁₂] M₂) (x : M₁) : (f + g) x = f x + g x :=
  rfl

@[simp, norm_cast]
theorem coe_add (f g : M₁ →SL[σ₁₂] M₂) : (↑(f + g) : M₁ →ₛₗ[σ₁₂] M₂) = f + g :=
  rfl

@[norm_cast]
theorem coe_add' (f g : M₁ →SL[σ₁₂] M₂) : ⇑(f + g) = f + g :=
  rfl

instance addCommMonoid : AddCommMonoid (M₁ →SL[σ₁₂] M₂) where
  zero_add := by
    intros
    ext
    apply_rules [zero_add, add_assoc, add_zero, neg_add_cancel, add_comm]
  add_zero := by
    intros
    ext
    apply_rules [zero_add, add_assoc, add_zero, neg_add_cancel, add_comm]
  add_comm := by
    intros
    ext
    apply_rules [zero_add, add_assoc, add_zero, neg_add_cancel, add_comm]
  add_assoc := by
    intros
    ext
    apply_rules [zero_add, add_assoc, add_zero, neg_add_cancel, add_comm]
  nsmul := (· • ·)
  nsmul_zero f := by
    ext
    simp
  nsmul_succ n f := by
    ext
    simp [add_smul]

@[simp, norm_cast]
theorem coe_sum {ι : Type*} (t : Finset ι) (f : ι → M₁ →SL[σ₁₂] M₂) :
    ↑(∑ d ∈ t, f d) = (∑ d ∈ t, f d : M₁ →ₛₗ[σ₁₂] M₂) :=
  map_sum (AddMonoidHom.mk ⟨((↑) : (M₁ →SL[σ₁₂] M₂) → M₁ →ₛₗ[σ₁₂] M₂), rfl⟩ fun _ _ => rfl) _ _

@[simp, norm_cast]
theorem coe_sum' {ι : Type*} (t : Finset ι) (f : ι → M₁ →SL[σ₁₂] M₂) :
    ⇑(∑ d ∈ t, f d) = ∑ d ∈ t, ⇑(f d) := by simp only [← coe_coe, coe_sum, LinearMap.coeFn_sum]

theorem sum_apply {ι : Type*} (t : Finset ι) (f : ι → M₁ →SL[σ₁₂] M₂) (b : M₁) :
    (∑ d ∈ t, f d) b = ∑ d ∈ t, f d b := by simp only [coe_sum', Finset.sum_apply]

end Add

variable [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

def comp (g : M₂ →SL[σ₂₃] M₃) (f : M₁ →SL[σ₁₂] M₂) : M₁ →SL[σ₁₃] M₃ :=
  ⟨(g : M₂ →ₛₗ[σ₂₃] M₃).comp (f : M₁ →ₛₗ[σ₁₂] M₂), g.2.comp f.2⟩

infixr:80 " ∘L " =>

  @ContinuousLinearMap.comp _ _ _ _ _ _ (RingHom.id _) (RingHom.id _) (RingHom.id _) _ _ _ _ _ _ _ _

    _ _ _ _ RingHomCompTriple.ids

@[simp, norm_cast]
theorem coe_comp (h : M₂ →SL[σ₂₃] M₃) (f : M₁ →SL[σ₁₂] M₂) :
    (h.comp f : M₁ →ₛₗ[σ₁₃] M₃) = (h : M₂ →ₛₗ[σ₂₃] M₃).comp (f : M₁ →ₛₗ[σ₁₂] M₂) :=
  rfl

@[simp, norm_cast]
theorem coe_comp' (h : M₂ →SL[σ₂₃] M₃) (f : M₁ →SL[σ₁₂] M₂) : ⇑(h.comp f) = h ∘ f :=
  rfl

theorem comp_apply (g : M₂ →SL[σ₂₃] M₃) (f : M₁ →SL[σ₁₂] M₂) (x : M₁) : (g.comp f) x = g (f x) :=
  rfl

@[simp]
theorem comp_id (f : M₁ →SL[σ₁₂] M₂) : f.comp (id R₁ M₁) = f :=
  ext fun _x => rfl

@[simp]
theorem id_comp (f : M₁ →SL[σ₁₂] M₂) : (id R₂ M₂).comp f = f :=
  ext fun _x => rfl

@[simp]
theorem comp_zero (g : M₂ →SL[σ₂₃] M₃) : g.comp (0 : M₁ →SL[σ₁₂] M₂) = 0 := by
  ext
  simp

@[simp]
theorem zero_comp (f : M₁ →SL[σ₁₂] M₂) : (0 : M₂ →SL[σ₂₃] M₃).comp f = 0 := by
  ext
  simp

@[simp]
theorem comp_add [ContinuousAdd M₂] [ContinuousAdd M₃] (g : M₂ →SL[σ₂₃] M₃)
    (f₁ f₂ : M₁ →SL[σ₁₂] M₂) : g.comp (f₁ + f₂) = g.comp f₁ + g.comp f₂ := by
  ext
  simp

@[simp]
theorem add_comp [ContinuousAdd M₃] (g₁ g₂ : M₂ →SL[σ₂₃] M₃) (f : M₁ →SL[σ₁₂] M₂) :
    (g₁ + g₂).comp f = g₁.comp f + g₂.comp f := by
  ext
  simp

theorem comp_finset_sum {ι : Type*} {s : Finset ι}
    [ContinuousAdd M₂] [ContinuousAdd M₃] (g : M₂ →SL[σ₂₃] M₃)
    (f : ι → M₁ →SL[σ₁₂] M₂) : g.comp (∑ i ∈ s, f i) = ∑ i ∈ s, g.comp (f i) := by
  ext
  simp

theorem finset_sum_comp {ι : Type*} {s : Finset ι}
    [ContinuousAdd M₃] (g : ι → M₂ →SL[σ₂₃] M₃)
    (f : M₁ →SL[σ₁₂] M₂) : (∑ i ∈ s, g i).comp f = ∑ i ∈ s, (g i).comp f := by
  ext
  simp only [coe_comp', coe_sum', Function.comp_apply, Finset.sum_apply]

theorem comp_assoc {R₄ : Type*} [Semiring R₄] [Module R₄ M₄] {σ₁₄ : R₁ →+* R₄} {σ₂₄ : R₂ →+* R₄}
    {σ₃₄ : R₃ →+* R₄} [RingHomCompTriple σ₁₃ σ₃₄ σ₁₄] [RingHomCompTriple σ₂₃ σ₃₄ σ₂₄]
    [RingHomCompTriple σ₁₂ σ₂₄ σ₁₄] (h : M₃ →SL[σ₃₄] M₄) (g : M₂ →SL[σ₂₃] M₃) (f : M₁ →SL[σ₁₂] M₂) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

instance instMul : Mul (M₁ →L[R₁] M₁) :=
  ⟨comp⟩

theorem mul_def (f g : M₁ →L[R₁] M₁) : f * g = f.comp g :=
  rfl

@[simp]
theorem coe_mul (f g : M₁ →L[R₁] M₁) : ⇑(f * g) = f ∘ g :=
  rfl

theorem mul_apply (f g : M₁ →L[R₁] M₁) (x : M₁) : (f * g) x = f (g x) :=
  rfl

instance monoidWithZero : MonoidWithZero (M₁ →L[R₁] M₁) where
  mul_zero f := ext fun _ => map_zero f
  zero_mul _ := ext fun _ => rfl
  mul_one _ := ext fun _ => rfl
  one_mul _ := ext fun _ => rfl
  mul_assoc _ _ _ := ext fun _ => rfl

theorem coe_pow (f : M₁ →L[R₁] M₁) (n : ℕ) : ⇑(f ^ n) = f^[n] :=
  hom_coe_pow _ rfl (fun _ _ ↦ rfl) _ _

instance instNatCast [ContinuousAdd M₁] : NatCast (M₁ →L[R₁] M₁) where
  natCast n := n • (1 : M₁ →L[R₁] M₁)

instance semiring [ContinuousAdd M₁] : Semiring (M₁ →L[R₁] M₁) where
  __ := ContinuousLinearMap.monoidWithZero
  __ := ContinuousLinearMap.addCommMonoid
  left_distrib f g h := ext fun x => map_add f (g x) (h x)
  right_distrib _ _ _ := ext fun _ => LinearMap.add_apply _ _ _
  toNatCast := instNatCast
  natCast_zero := zero_smul ℕ (1 : M₁ →L[R₁] M₁)
  natCast_succ n := AddMonoid.nsmul_succ n (1 : M₁ →L[R₁] M₁)

@[simps]
def toLinearMapRingHom [ContinuousAdd M₁] : (M₁ →L[R₁] M₁) →+* M₁ →ₗ[R₁] M₁ where
  toFun := toLinearMap
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

@[simp]
theorem natCast_apply [ContinuousAdd M₁] (n : ℕ) (m : M₁) : (↑n : M₁ →L[R₁] M₁) m = n • m :=
  rfl

@[simp]
theorem ofNat_apply [ContinuousAdd M₁] (n : ℕ) [n.AtLeastTwo] (m : M₁) :
    ((no_index (OfNat.ofNat n) : M₁ →L[R₁] M₁)) m = OfNat.ofNat n • m :=
  rfl

section ApplyAction

variable [ContinuousAdd M₁]

instance applyModule : Module (M₁ →L[R₁] M₁) M₁ :=
  Module.compHom _ toLinearMapRingHom

@[simp]
protected theorem smul_def (f : M₁ →L[R₁] M₁) (a : M₁) : f • a = f a :=
  rfl

instance applyFaithfulSMul : FaithfulSMul (M₁ →L[R₁] M₁) M₁ :=
  ⟨fun {_ _} => ContinuousLinearMap.ext⟩

instance applySMulCommClass : SMulCommClass R₁ (M₁ →L[R₁] M₁) M₁ where
  smul_comm r e m := (e.map_smul r m).symm

instance applySMulCommClass' : SMulCommClass (M₁ →L[R₁] M₁) R₁ M₁ where
  smul_comm := ContinuousLinearMap.map_smul

instance continuousConstSMul_apply : ContinuousConstSMul (M₁ →L[R₁] M₁) M₁ :=
  ⟨ContinuousLinearMap.continuous⟩

end ApplyAction

protected def prod [Module R₁ M₂] [Module R₁ M₃] (f₁ : M₁ →L[R₁] M₂) (f₂ : M₁ →L[R₁] M₃) :
    M₁ →L[R₁] M₂ × M₃ :=
  ⟨(f₁ : M₁ →ₗ[R₁] M₂).prod f₂, f₁.2.prod_mk f₂.2⟩

@[simp, norm_cast]
theorem coe_prod [Module R₁ M₂] [Module R₁ M₃] (f₁ : M₁ →L[R₁] M₂) (f₂ : M₁ →L[R₁] M₃) :
    (f₁.prod f₂ : M₁ →ₗ[R₁] M₂ × M₃) = LinearMap.prod f₁ f₂ :=
  rfl

@[simp, norm_cast]
theorem prod_apply [Module R₁ M₂] [Module R₁ M₃] (f₁ : M₁ →L[R₁] M₂) (f₂ : M₁ →L[R₁] M₃) (x : M₁) :
    f₁.prod f₂ x = (f₁ x, f₂ x) :=
  rfl

section

variable (R₁ M₁ M₂)

def inl [Module R₁ M₂] : M₁ →L[R₁] M₁ × M₂ :=
  (id R₁ M₁).prod 0

def inr [Module R₁ M₂] : M₂ →L[R₁] M₁ × M₂ :=
  (0 : M₂ →L[R₁] M₁).prod (id R₁ M₂)

end

variable {F : Type*}

@[simp]
theorem inl_apply [Module R₁ M₂] (x : M₁) : inl R₁ M₁ M₂ x = (x, 0) :=
  rfl

@[simp]
theorem inr_apply [Module R₁ M₂] (x : M₂) : inr R₁ M₁ M₂ x = (0, x) :=
  rfl

@[simp, norm_cast]
theorem coe_inl [Module R₁ M₂] : (inl R₁ M₁ M₂ : M₁ →ₗ[R₁] M₁ × M₂) = LinearMap.inl R₁ M₁ M₂ :=
  rfl

@[simp, norm_cast]
theorem coe_inr [Module R₁ M₂] : (inr R₁ M₁ M₂ : M₂ →ₗ[R₁] M₁ × M₂) = LinearMap.inr R₁ M₁ M₂ :=
  rfl

theorem isClosed_ker [T1Space M₂] [FunLike F M₁ M₂] [ContinuousSemilinearMapClass F σ₁₂ M₁ M₂]
    (f : F) :
    IsClosed (ker f : Set M₁) :=
  continuous_iff_isClosed.1 (map_continuous f) _ isClosed_singleton

theorem isComplete_ker {M' : Type*} [UniformSpace M'] [CompleteSpace M'] [AddCommMonoid M']
    [Module R₁ M'] [T1Space M₂] [FunLike F M' M₂] [ContinuousSemilinearMapClass F σ₁₂ M' M₂]
    (f : F) :
    IsComplete (ker f : Set M') :=
  (isClosed_ker f).isComplete

instance completeSpace_ker {M' : Type*} [UniformSpace M'] [CompleteSpace M']
    [AddCommMonoid M'] [Module R₁ M'] [T1Space M₂]
    [FunLike F M' M₂] [ContinuousSemilinearMapClass F σ₁₂ M' M₂]
    (f : F) : CompleteSpace (ker f) :=
  (isComplete_ker f).completeSpace_coe

instance completeSpace_eqLocus {M' : Type*} [UniformSpace M'] [CompleteSpace M']
    [AddCommMonoid M'] [Module R₁ M'] [T2Space M₂]
    [FunLike F M' M₂] [ContinuousSemilinearMapClass F σ₁₂ M' M₂]
    (f g : F) : CompleteSpace (LinearMap.eqLocus f g) :=
  IsClosed.completeSpace_coe <| isClosed_eq (map_continuous f) (map_continuous g)

@[simp]
theorem ker_prod [Module R₁ M₂] [Module R₁ M₃] (f : M₁ →L[R₁] M₂) (g : M₁ →L[R₁] M₃) :
    ker (f.prod g) = ker f ⊓ ker g :=
  LinearMap.ker_prod (f : M₁ →ₗ[R₁] M₂) (g : M₁ →ₗ[R₁] M₃)

def codRestrict (f : M₁ →SL[σ₁₂] M₂) (p : Submodule R₂ M₂) (h : ∀ x, f x ∈ p) :
    M₁ →SL[σ₁₂] p where
  cont := f.continuous.subtype_mk _
  toLinearMap := (f : M₁ →ₛₗ[σ₁₂] M₂).codRestrict p h

@[norm_cast]
theorem coe_codRestrict (f : M₁ →SL[σ₁₂] M₂) (p : Submodule R₂ M₂) (h : ∀ x, f x ∈ p) :
    (f.codRestrict p h : M₁ →ₛₗ[σ₁₂] p) = (f : M₁ →ₛₗ[σ₁₂] M₂).codRestrict p h :=
  rfl

@[simp]
theorem coe_codRestrict_apply (f : M₁ →SL[σ₁₂] M₂) (p : Submodule R₂ M₂) (h : ∀ x, f x ∈ p) (x) :
    (f.codRestrict p h x : M₂) = f x :=
  rfl

@[simp]
theorem ker_codRestrict (f : M₁ →SL[σ₁₂] M₂) (p : Submodule R₂ M₂) (h : ∀ x, f x ∈ p) :
    ker (f.codRestrict p h) = ker f :=
  (f : M₁ →ₛₗ[σ₁₂] M₂).ker_codRestrict p h

abbrev rangeRestrict [RingHomSurjective σ₁₂] (f : M₁ →SL[σ₁₂] M₂) :=
  f.codRestrict (LinearMap.range f) (LinearMap.mem_range_self f)

@[simp]
theorem coe_rangeRestrict [RingHomSurjective σ₁₂] (f : M₁ →SL[σ₁₂] M₂) :
    (f.rangeRestrict : M₁ →ₛₗ[σ₁₂] LinearMap.range f) = (f : M₁ →ₛₗ[σ₁₂] M₂).rangeRestrict :=
  rfl

def _root_.Submodule.subtypeL (p : Submodule R₁ M₁) : p →L[R₁] M₁ where
  cont := continuous_subtype_val
  toLinearMap := p.subtype

@[simp, norm_cast]
theorem _root_.Submodule.coe_subtypeL (p : Submodule R₁ M₁) :
    (p.subtypeL : p →ₗ[R₁] M₁) = p.subtype :=
  rfl

@[simp]
theorem _root_.Submodule.coe_subtypeL' (p : Submodule R₁ M₁) : ⇑p.subtypeL = p.subtype :=
  rfl

@[simp] -- @[norm_cast] -- Porting note: A theorem with this can't have a rhs starting with `↑`.

theorem _root_.Submodule.subtypeL_apply (p : Submodule R₁ M₁) (x : p) : p.subtypeL x = x :=
  rfl

@[simp]
theorem _root_.Submodule.range_subtypeL (p : Submodule R₁ M₁) : range p.subtypeL = p :=
  Submodule.range_subtype _

@[simp]
theorem _root_.Submodule.ker_subtypeL (p : Submodule R₁ M₁) : ker p.subtypeL = ⊥ :=
  Submodule.ker_subtype _

variable (R₁ M₁ M₂)

def fst [Module R₁ M₂] : M₁ × M₂ →L[R₁] M₁ where
  cont := continuous_fst
  toLinearMap := LinearMap.fst R₁ M₁ M₂

def snd [Module R₁ M₂] : M₁ × M₂ →L[R₁] M₂ where
  cont := continuous_snd
  toLinearMap := LinearMap.snd R₁ M₁ M₂

variable {R₁ M₁ M₂}

@[simp, norm_cast]
theorem coe_fst [Module R₁ M₂] : ↑(fst R₁ M₁ M₂) = LinearMap.fst R₁ M₁ M₂ :=
  rfl

@[simp, norm_cast]
theorem coe_fst' [Module R₁ M₂] : ⇑(fst R₁ M₁ M₂) = Prod.fst :=
  rfl

@[simp, norm_cast]
theorem coe_snd [Module R₁ M₂] : ↑(snd R₁ M₁ M₂) = LinearMap.snd R₁ M₁ M₂ :=
  rfl

@[simp, norm_cast]
theorem coe_snd' [Module R₁ M₂] : ⇑(snd R₁ M₁ M₂) = Prod.snd :=
  rfl

@[simp]
theorem fst_prod_snd [Module R₁ M₂] : (fst R₁ M₁ M₂).prod (snd R₁ M₁ M₂) = id R₁ (M₁ × M₂) :=
  ext fun ⟨_x, _y⟩ => rfl

@[simp]
theorem fst_comp_prod [Module R₁ M₂] [Module R₁ M₃] (f : M₁ →L[R₁] M₂) (g : M₁ →L[R₁] M₃) :
    (fst R₁ M₂ M₃).comp (f.prod g) = f :=
  ext fun _x => rfl

@[simp]
theorem snd_comp_prod [Module R₁ M₂] [Module R₁ M₃] (f : M₁ →L[R₁] M₂) (g : M₁ →L[R₁] M₃) :
    (snd R₁ M₂ M₃).comp (f.prod g) = g :=
  ext fun _x => rfl

def prodMap [Module R₁ M₂] [Module R₁ M₃] [Module R₁ M₄] (f₁ : M₁ →L[R₁] M₂) (f₂ : M₃ →L[R₁] M₄) :
    M₁ × M₃ →L[R₁] M₂ × M₄ :=
  (f₁.comp (fst R₁ M₁ M₃)).prod (f₂.comp (snd R₁ M₁ M₃))

@[simp, norm_cast]
theorem coe_prodMap [Module R₁ M₂] [Module R₁ M₃] [Module R₁ M₄] (f₁ : M₁ →L[R₁] M₂)
    (f₂ : M₃ →L[R₁] M₄) : ↑(f₁.prodMap f₂) = (f₁ : M₁ →ₗ[R₁] M₂).prodMap (f₂ : M₃ →ₗ[R₁] M₄) :=
  rfl

@[simp, norm_cast]
theorem coe_prodMap' [Module R₁ M₂] [Module R₁ M₃] [Module R₁ M₄] (f₁ : M₁ →L[R₁] M₂)
    (f₂ : M₃ →L[R₁] M₄) : ⇑(f₁.prodMap f₂) = Prod.map f₁ f₂ :=
  rfl

def coprod [Module R₁ M₂] [Module R₁ M₃] [ContinuousAdd M₃] (f₁ : M₁ →L[R₁] M₃)
    (f₂ : M₂ →L[R₁] M₃) : M₁ × M₂ →L[R₁] M₃ :=
  ⟨LinearMap.coprod f₁ f₂, (f₁.cont.comp continuous_fst).add (f₂.cont.comp continuous_snd)⟩

@[norm_cast, simp]
theorem coe_coprod [Module R₁ M₂] [Module R₁ M₃] [ContinuousAdd M₃] (f₁ : M₁ →L[R₁] M₃)
    (f₂ : M₂ →L[R₁] M₃) : (f₁.coprod f₂ : M₁ × M₂ →ₗ[R₁] M₃) = LinearMap.coprod f₁ f₂ :=
  rfl

@[simp]
theorem coprod_apply [Module R₁ M₂] [Module R₁ M₃] [ContinuousAdd M₃] (f₁ : M₁ →L[R₁] M₃)
    (f₂ : M₂ →L[R₁] M₃) (x) : f₁.coprod f₂ x = f₁ x.1 + f₂ x.2 :=
  rfl

theorem range_coprod [Module R₁ M₂] [Module R₁ M₃] [ContinuousAdd M₃] (f₁ : M₁ →L[R₁] M₃)
    (f₂ : M₂ →L[R₁] M₃) : range (f₁.coprod f₂) = range f₁ ⊔ range f₂ :=
  LinearMap.range_coprod _ _

theorem comp_fst_add_comp_snd [Module R₁ M₂] [Module R₁ M₃] [ContinuousAdd M₃] (f : M₁ →L[R₁] M₃)
    (g : M₂ →L[R₁] M₃) :
    f.comp (ContinuousLinearMap.fst R₁ M₁ M₂) + g.comp (ContinuousLinearMap.snd R₁ M₁ M₂) =
      f.coprod g :=
  rfl

theorem coprod_inl_inr [ContinuousAdd M₁] [ContinuousAdd M'₁] :
    (ContinuousLinearMap.inl R₁ M₁ M'₁).coprod (ContinuousLinearMap.inr R₁ M₁ M'₁) =
      ContinuousLinearMap.id R₁ (M₁ × M'₁) := by
  apply coe_injective; apply LinearMap.coprod_inl_inr

section

variable {R S : Type*} [Semiring R] [Semiring S] [Module R M₁] [Module R M₂] [Module R S]
  [Module S M₂] [IsScalarTower R S M₂] [TopologicalSpace S] [ContinuousSMul S M₂]

def smulRight (c : M₁ →L[R] S) (f : M₂) : M₁ →L[R] M₂ :=
  { c.toLinearMap.smulRight f with cont := c.2.smul continuous_const }

@[simp]
theorem smulRight_apply {c : M₁ →L[R] S} {f : M₂} {x : M₁} :
    (smulRight c f : M₁ → M₂) x = c x • f :=
  rfl

end

variable [Module R₁ M₂] [TopologicalSpace R₁] [ContinuousSMul R₁ M₂]

-- DISSOLVED: smulRight_one_one

@[simp]
theorem smulRight_one_eq_iff {f f' : M₂} :
    smulRight (1 : R₁ →L[R₁] R₁) f = smulRight (1 : R₁ →L[R₁] R₁) f' ↔ f = f' := by
  simp only [ContinuousLinearMap.ext_ring_iff, smulRight_apply, one_apply, one_smul]

theorem smulRight_comp [ContinuousMul R₁] {x : M₂} {c : R₁} :
    (smulRight (1 : R₁ →L[R₁] R₁) x).comp (smulRight (1 : R₁ →L[R₁] R₁) c) =
      smulRight (1 : R₁ →L[R₁] R₁) (c • x) := by
  ext
  simp [mul_smul]

section ToSpanSingleton

variable (R₁)

variable [ContinuousSMul R₁ M₁]

def toSpanSingleton (x : M₁) : R₁ →L[R₁] M₁ where
  toLinearMap := LinearMap.toSpanSingleton R₁ M₁ x
  cont := continuous_id.smul continuous_const

theorem toSpanSingleton_apply (x : M₁) (r : R₁) : toSpanSingleton R₁ x r = r • x :=
  rfl

theorem toSpanSingleton_add [ContinuousAdd M₁] (x y : M₁) :
    toSpanSingleton R₁ (x + y) = toSpanSingleton R₁ x + toSpanSingleton R₁ y := by
  ext1; simp [toSpanSingleton_apply]

theorem toSpanSingleton_smul' {α} [Monoid α] [DistribMulAction α M₁] [ContinuousConstSMul α M₁]
    [SMulCommClass R₁ α M₁] (c : α) (x : M₁) :
    toSpanSingleton R₁ (c • x) = c • toSpanSingleton R₁ x := by
  ext1; rw [toSpanSingleton_apply, smul_apply, toSpanSingleton_apply, smul_comm]

theorem toSpanSingleton_smul (R) {M₁} [CommSemiring R] [AddCommMonoid M₁] [Module R M₁]
    [TopologicalSpace R] [TopologicalSpace M₁] [ContinuousSMul R M₁] (c : R) (x : M₁) :
    toSpanSingleton R (c • x) = c • toSpanSingleton R x :=
  toSpanSingleton_smul' R c x

end ToSpanSingleton

end Semiring

section Pi

variable {R : Type*} [Semiring R] {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [Module R M]
  {M₂ : Type*} [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M₂] {ι : Type*} {φ : ι → Type*}
  [∀ i, TopologicalSpace (φ i)] [∀ i, AddCommMonoid (φ i)] [∀ i, Module R (φ i)]

def pi (f : ∀ i, M →L[R] φ i) : M →L[R] ∀ i, φ i :=
  ⟨LinearMap.pi fun i => f i, continuous_pi fun i => (f i).continuous⟩

@[simp]
theorem coe_pi' (f : ∀ i, M →L[R] φ i) : ⇑(pi f) = fun c i => f i c :=
  rfl

@[simp]
theorem coe_pi (f : ∀ i, M →L[R] φ i) : (pi f : M →ₗ[R] ∀ i, φ i) = LinearMap.pi fun i => f i :=
  rfl

theorem pi_apply (f : ∀ i, M →L[R] φ i) (c : M) (i : ι) : pi f c i = f i c :=
  rfl

theorem pi_eq_zero (f : ∀ i, M →L[R] φ i) : pi f = 0 ↔ ∀ i, f i = 0 := by
  simp only [ContinuousLinearMap.ext_iff, pi_apply, funext_iff]
  exact forall_swap

theorem pi_zero : pi (fun _ => 0 : ∀ i, M →L[R] φ i) = 0 :=
  ext fun _ => rfl

theorem pi_comp (f : ∀ i, M →L[R] φ i) (g : M₂ →L[R] M) :
    (pi f).comp g = pi fun i => (f i).comp g :=
  rfl

def proj (i : ι) : (∀ i, φ i) →L[R] φ i :=
  ⟨LinearMap.proj i, continuous_apply _⟩

@[simp]
theorem proj_apply (i : ι) (b : ∀ i, φ i) : (proj i : (∀ i, φ i) →L[R] φ i) b = b i :=
  rfl

theorem proj_pi (f : ∀ i, M₂ →L[R] φ i) (i : ι) : (proj i).comp (pi f) = f i :=
  ext fun _c => rfl

theorem iInf_ker_proj : (⨅ i, ker (proj i : (∀ i, φ i) →L[R] φ i) : Submodule R (∀ i, φ i)) = ⊥ :=
  LinearMap.iInf_ker_proj

variable (R φ)

def _root_.Pi.compRightL {α : Type*} (f : α → ι) : ((i : ι) → φ i) →L[R] ((i : α) → φ (f i)) where
  toFun := fun v i ↦ v (f i)
  map_add' := by intros; ext; simp
  map_smul' := by intros; ext; simp
  cont := by continuity

@[simp] lemma _root_.Pi.compRightL_apply {α : Type*} (f : α → ι) (v : (i : ι) → φ i) (i : α) :
    Pi.compRightL R φ f v i = v (f i) := rfl

def iInfKerProjEquiv {I J : Set ι} [DecidablePred fun i => i ∈ I] (hd : Disjoint I J)
    (hu : Set.univ ⊆ I ∪ J) :
    (⨅ i ∈ J, ker (proj i : (∀ i, φ i) →L[R] φ i) :
    Submodule R (∀ i, φ i)) ≃L[R] ∀ i : I, φ i where
  toLinearEquiv := LinearMap.iInfKerProjEquiv R φ hd hu
  continuous_toFun :=
    continuous_pi fun i =>
      Continuous.comp (continuous_apply (π := φ) i) <|
        @continuous_subtype_val _ _ fun x =>
          x ∈ (⨅ i ∈ J, ker (proj i : (∀ i, φ i) →L[R] φ i) : Submodule R (∀ i, φ i))
  continuous_invFun :=
    Continuous.subtype_mk
      (continuous_pi fun i => by
        dsimp
        split_ifs <;> [apply continuous_apply; exact continuous_zero])
      _

end Pi

section Ring

variable {R : Type*} [Ring R] {R₂ : Type*} [Ring R₂] {R₃ : Type*} [Ring R₃] {M : Type*}
  [TopologicalSpace M] [AddCommGroup M] {M₂ : Type*} [TopologicalSpace M₂] [AddCommGroup M₂]
  {M₃ : Type*} [TopologicalSpace M₃] [AddCommGroup M₃] {M₄ : Type*} [TopologicalSpace M₄]
  [AddCommGroup M₄] [Module R M] [Module R₂ M₂] [Module R₃ M₃] {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃}
  {σ₁₃ : R →+* R₃}

section

protected theorem map_neg (f : M →SL[σ₁₂] M₂) (x : M) : f (-x) = -f x := by
  exact map_neg f x

protected theorem map_sub (f : M →SL[σ₁₂] M₂) (x y : M) : f (x - y) = f x - f y := by
  exact map_sub f x y

@[simp]
theorem sub_apply' (f g : M →SL[σ₁₂] M₂) (x : M) : ((f : M →ₛₗ[σ₁₂] M₂) - g) x = f x - g x :=
  rfl

end

section

variable [Module R M₂] [Module R M₃] [Module R M₄]

theorem range_prod_eq {f : M →L[R] M₂} {g : M →L[R] M₃} (h : ker f ⊔ ker g = ⊤) :
    range (f.prod g) = (range f).prod (range g) :=
  LinearMap.range_prod_eq h

theorem ker_prod_ker_le_ker_coprod [ContinuousAdd M₃] (f : M →L[R] M₃) (g : M₂ →L[R] M₃) :
    (LinearMap.ker f).prod (LinearMap.ker g) ≤ LinearMap.ker (f.coprod g) :=
  LinearMap.ker_prod_ker_le_ker_coprod f.toLinearMap g.toLinearMap

theorem ker_coprod_of_disjoint_range [ContinuousAdd M₃] (f : M →L[R] M₃) (g : M₂ →L[R] M₃)
    (hd : Disjoint (range f) (range g)) :
    LinearMap.ker (f.coprod g) = (LinearMap.ker f).prod (LinearMap.ker g) :=
  LinearMap.ker_coprod_of_disjoint_range f.toLinearMap g.toLinearMap hd

end

section

variable [TopologicalAddGroup M₂]

instance neg : Neg (M →SL[σ₁₂] M₂) :=
  ⟨fun f => ⟨-f, f.2.neg⟩⟩

@[simp]
theorem neg_apply (f : M →SL[σ₁₂] M₂) (x : M) : (-f) x = -f x :=
  rfl

@[simp, norm_cast]
theorem coe_neg (f : M →SL[σ₁₂] M₂) : (↑(-f) : M →ₛₗ[σ₁₂] M₂) = -f :=
  rfl

@[norm_cast]
theorem coe_neg' (f : M →SL[σ₁₂] M₂) : ⇑(-f) = -f :=
  rfl

instance sub : Sub (M →SL[σ₁₂] M₂) :=
  ⟨fun f g => ⟨f - g, f.2.sub g.2⟩⟩

instance addCommGroup : AddCommGroup (M →SL[σ₁₂] M₂) where
  __ := ContinuousLinearMap.addCommMonoid
  neg := (-·)
  sub := (· - ·)
  sub_eq_add_neg _ _ := by ext; apply sub_eq_add_neg
  nsmul := (· • ·)
  zsmul := (· • ·)
  zsmul_zero' f := by ext; simp
  zsmul_succ' n f := by ext; simp [add_smul, add_comm]
  zsmul_neg' n f := by ext; simp [add_smul]
  neg_add_cancel _ := by ext; apply neg_add_cancel

theorem sub_apply (f g : M →SL[σ₁₂] M₂) (x : M) : (f - g) x = f x - g x :=
  rfl

@[simp, norm_cast]
theorem coe_sub (f g : M →SL[σ₁₂] M₂) : (↑(f - g) : M →ₛₗ[σ₁₂] M₂) = f - g :=
  rfl

@[simp, norm_cast]
theorem coe_sub' (f g : M →SL[σ₁₂] M₂) : ⇑(f - g) = f - g :=
  rfl

end

@[simp]
theorem comp_neg [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [TopologicalAddGroup M₂] [TopologicalAddGroup M₃]
    (g : M₂ →SL[σ₂₃] M₃) (f : M →SL[σ₁₂] M₂) : g.comp (-f) = -g.comp f := by
  ext x
  simp

@[simp]
theorem neg_comp [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [TopologicalAddGroup M₃] (g : M₂ →SL[σ₂₃] M₃)
    (f : M →SL[σ₁₂] M₂) : (-g).comp f = -g.comp f := by
  ext
  simp

@[simp]
theorem comp_sub [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [TopologicalAddGroup M₂] [TopologicalAddGroup M₃]
    (g : M₂ →SL[σ₂₃] M₃) (f₁ f₂ : M →SL[σ₁₂] M₂) : g.comp (f₁ - f₂) = g.comp f₁ - g.comp f₂ := by
  ext
  simp

@[simp]
theorem sub_comp [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [TopologicalAddGroup M₃] (g₁ g₂ : M₂ →SL[σ₂₃] M₃)
    (f : M →SL[σ₁₂] M₂) : (g₁ - g₂).comp f = g₁.comp f - g₂.comp f := by
  ext
  simp

instance ring [TopologicalAddGroup M] : Ring (M →L[R] M) where
  __ := ContinuousLinearMap.semiring
  __ := ContinuousLinearMap.addCommGroup
  intCast z := z • (1 : M →L[R] M)
  intCast_ofNat := natCast_zsmul _
  intCast_negSucc := negSucc_zsmul _

@[simp]
theorem intCast_apply [TopologicalAddGroup M] (z : ℤ) (m : M) : (↑z : M →L[R] M) m = z • m :=
  rfl

theorem smulRight_one_pow [TopologicalSpace R] [TopologicalRing R] (c : R) (n : ℕ) :
    smulRight (1 : R →L[R] R) c ^ n = smulRight (1 : R →L[R] R) (c ^ n) := by
  induction n with
  | zero => ext; simp
  | succ n ihn => rw [pow_succ, ihn, mul_def, smulRight_comp, smul_eq_mul, pow_succ']

section

variable {σ₂₁ : R₂ →+* R} [RingHomInvPair σ₁₂ σ₂₁]

def projKerOfRightInverse [TopologicalAddGroup M] (f₁ : M →SL[σ₁₂] M₂) (f₂ : M₂ →SL[σ₂₁] M)
    (h : Function.RightInverse f₂ f₁) : M →L[R] LinearMap.ker f₁ :=
  (id R M - f₂.comp f₁).codRestrict (LinearMap.ker f₁) fun x => by simp [h (f₁ x)]

@[simp]
theorem coe_projKerOfRightInverse_apply [TopologicalAddGroup M] (f₁ : M →SL[σ₁₂] M₂)
    (f₂ : M₂ →SL[σ₂₁] M) (h : Function.RightInverse f₂ f₁) (x : M) :
    (f₁.projKerOfRightInverse f₂ h x : M) = x - f₂ (f₁ x) :=
  rfl

@[simp]
theorem projKerOfRightInverse_apply_idem [TopologicalAddGroup M] (f₁ : M →SL[σ₁₂] M₂)
    (f₂ : M₂ →SL[σ₂₁] M) (h : Function.RightInverse f₂ f₁) (x : LinearMap.ker f₁) :
    f₁.projKerOfRightInverse f₂ h x = x := by
  ext1
  simp

@[simp]
theorem projKerOfRightInverse_comp_inv [TopologicalAddGroup M] (f₁ : M →SL[σ₁₂] M₂)
    (f₂ : M₂ →SL[σ₂₁] M) (h : Function.RightInverse f₂ f₁) (y : M₂) :
    f₁.projKerOfRightInverse f₂ h (f₂ y) = 0 :=
  Subtype.ext_iff_val.2 <| by simp [h y]

end

end Ring

section DivisionMonoid

variable {R M : Type*}

-- DISSOLVED: isOpenMap_of_ne_zero

end DivisionMonoid

section SMulMonoid

variable {R R₂ R₃ S S₃ : Type*} [Semiring R] [Semiring R₂] [Semiring R₃] [Monoid S] [Monoid S₃]
  {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [Module R M] {M₂ : Type*}
  [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R₂ M₂] {M₃ : Type*} [TopologicalSpace M₃]
  [AddCommMonoid M₃] [Module R₃ M₃] {N₂ : Type*} [TopologicalSpace N₂] [AddCommMonoid N₂]
  [Module R N₂] {N₃ : Type*} [TopologicalSpace N₃] [AddCommMonoid N₃] [Module R N₃]
  [DistribMulAction S₃ M₃] [SMulCommClass R₃ S₃ M₃] [ContinuousConstSMul S₃ M₃]
  [DistribMulAction S N₃] [SMulCommClass R S N₃] [ContinuousConstSMul S N₃] {σ₁₂ : R →+* R₂}
  {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

@[simp]
theorem smul_comp (c : S₃) (h : M₂ →SL[σ₂₃] M₃) (f : M →SL[σ₁₂] M₂) :
    (c • h).comp f = c • h.comp f :=
  rfl

variable [DistribMulAction S₃ M₂] [ContinuousConstSMul S₃ M₂] [SMulCommClass R₂ S₃ M₂]

variable [DistribMulAction S N₂] [ContinuousConstSMul S N₂] [SMulCommClass R S N₂]

@[simp]
theorem comp_smul [LinearMap.CompatibleSMul N₂ N₃ S R] (hₗ : N₂ →L[R] N₃) (c : S)
    (fₗ : M →L[R] N₂) : hₗ.comp (c • fₗ) = c • hₗ.comp fₗ := by
  ext x
  exact hₗ.map_smul_of_tower c (fₗ x)

@[simp]
theorem comp_smulₛₗ [SMulCommClass R₂ R₂ M₂] [SMulCommClass R₃ R₃ M₃] [ContinuousConstSMul R₂ M₂]
    [ContinuousConstSMul R₃ M₃] (h : M₂ →SL[σ₂₃] M₃) (c : R₂) (f : M →SL[σ₁₂] M₂) :
    h.comp (c • f) = σ₂₃ c • h.comp f := by
  ext x
  simp only [coe_smul', coe_comp', Function.comp_apply, Pi.smul_apply,
    ContinuousLinearMap.map_smulₛₗ]

instance distribMulAction [ContinuousAdd M₂] : DistribMulAction S₃ (M →SL[σ₁₂] M₂) where
  smul_add a f g := ext fun x => smul_add a (f x) (g x)
  smul_zero a := ext fun _ => smul_zero a

end SMulMonoid

section SMul

variable {R R₂ R₃ S S₃ : Type*} [Semiring R] [Semiring R₂] [Semiring R₃] [Semiring S] [Semiring S₃]
  {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [Module R M] {M₂ : Type*}
  [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R₂ M₂] {M₃ : Type*} [TopologicalSpace M₃]
  [AddCommMonoid M₃] [Module R₃ M₃] {N₂ : Type*} [TopologicalSpace N₂] [AddCommMonoid N₂]
  [Module R N₂] {N₃ : Type*} [TopologicalSpace N₃] [AddCommMonoid N₃] [Module R N₃] [Module S₃ M₃]
  [SMulCommClass R₃ S₃ M₃] [ContinuousConstSMul S₃ M₃] [Module S N₂] [ContinuousConstSMul S N₂]
  [SMulCommClass R S N₂] [Module S N₃] [SMulCommClass R S N₃] [ContinuousConstSMul S N₃]
  {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] (c : S)
  (h : M₂ →SL[σ₂₃] M₃) (f : M →SL[σ₁₂] M₂)

@[simps apply]
def prodEquiv : (M →L[R] N₂) × (M →L[R] N₃) ≃ (M →L[R] N₂ × N₃) where
  toFun f := f.1.prod f.2
  invFun f := ⟨(fst _ _ _).comp f, (snd _ _ _).comp f⟩
  left_inv f := by ext <;> rfl
  right_inv f := by ext <;> rfl

theorem prod_ext_iff {f g : M × N₂ →L[R] N₃} :
    f = g ↔ f.comp (inl _ _ _) = g.comp (inl _ _ _) ∧ f.comp (inr _ _ _) = g.comp (inr _ _ _) := by
  simp only [← coe_inj, LinearMap.prod_ext_iff]
  rfl

@[ext]
theorem prod_ext {f g : M × N₂ →L[R] N₃} (hl : f.comp (inl _ _ _) = g.comp (inl _ _ _))
    (hr : f.comp (inr _ _ _) = g.comp (inr _ _ _)) : f = g :=
  prod_ext_iff.2 ⟨hl, hr⟩

variable [ContinuousAdd M₂] [ContinuousAdd M₃] [ContinuousAdd N₂]

instance module : Module S₃ (M →SL[σ₁₃] M₃) where
  zero_smul _ := ext fun _ => zero_smul S₃ _
  add_smul _ _ _ := ext fun _ => add_smul _ _ _

instance isCentralScalar [Module S₃ᵐᵒᵖ M₃] [IsCentralScalar S₃ M₃] :
    IsCentralScalar S₃ (M →SL[σ₁₃] M₃) where
  op_smul_eq_smul _ _ := ext fun _ => op_smul_eq_smul _ _

variable (S) [ContinuousAdd N₃]

@[simps apply]
def prodₗ : ((M →L[R] N₂) × (M →L[R] N₃)) ≃ₗ[S] M →L[R] N₂ × N₃ :=
  { prodEquiv with
    map_add' := fun _f _g => rfl
    map_smul' := fun _c _f => rfl }

@[simps]
def coeLM : (M →L[R] N₃) →ₗ[S] M →ₗ[R] N₃ where
  toFun := (↑)
  map_add' f g := coe_add f g
  map_smul' c f := coe_smul c f

variable {S} (σ₁₃)

@[simps]
def coeLMₛₗ : (M →SL[σ₁₃] M₃) →ₗ[S₃] M →ₛₗ[σ₁₃] M₃ where
  toFun := (↑)
  map_add' f g := coe_add f g
  map_smul' c f := coe_smul c f

end SMul

section SMulRightₗ

variable {R S T M M₂ : Type*} [Semiring R] [Semiring S] [Semiring T] [Module R S]
  [AddCommMonoid M₂] [Module R M₂] [Module S M₂] [IsScalarTower R S M₂] [TopologicalSpace S]
  [TopologicalSpace M₂] [ContinuousSMul S M₂] [TopologicalSpace M] [AddCommMonoid M] [Module R M]
  [ContinuousAdd M₂] [Module T M₂] [ContinuousConstSMul T M₂] [SMulCommClass R T M₂]
  [SMulCommClass S T M₂]

def smulRightₗ (c : M →L[R] S) : M₂ →ₗ[T] M →L[R] M₂ where
  toFun := c.smulRight
  map_add' x y := by
    ext e
    apply smul_add (c e)
  map_smul' a x := by
    ext e
    dsimp
    apply smul_comm

@[simp]
theorem coe_smulRightₗ (c : M →L[R] S) : ⇑(smulRightₗ c : M₂ →ₗ[T] M →L[R] M₂) = c.smulRight :=
  rfl

end SMulRightₗ

section CommRing

variable {R : Type*} [CommRing R] {M : Type*} [TopologicalSpace M] [AddCommGroup M] {M₂ : Type*}
  [TopologicalSpace M₂] [AddCommGroup M₂] {M₃ : Type*} [TopologicalSpace M₃] [AddCommGroup M₃]
  [Module R M] [Module R M₂] [Module R M₃]

variable [TopologicalAddGroup M₂] [ContinuousConstSMul R M₂]

instance algebra : Algebra R (M₂ →L[R] M₂) :=
  Algebra.ofModule smul_comp fun _ _ _ => comp_smul _ _ _

@[simp] theorem algebraMap_apply (r : R) (m : M₂) : algebraMap R (M₂ →L[R] M₂) r m = r • m := rfl

end CommRing

section RestrictScalars

variable {A M M₂ : Type*} [Ring A] [AddCommGroup M] [AddCommGroup M₂] [Module A M] [Module A M₂]
  [TopologicalSpace M] [TopologicalSpace M₂] (R : Type*) [Ring R] [Module R M] [Module R M₂]
  [LinearMap.CompatibleSMul M M₂ R A]

def restrictScalars (f : M →L[A] M₂) : M →L[R] M₂ :=
  ⟨(f : M →ₗ[A] M₂).restrictScalars R, f.continuous⟩

variable {R}

@[simp] -- @[norm_cast] -- Porting note: This theorem can't be a `norm_cast` theorem.

theorem coe_restrictScalars (f : M →L[A] M₂) :
    (f.restrictScalars R : M →ₗ[R] M₂) = (f : M →ₗ[A] M₂).restrictScalars R :=
  rfl

@[simp]
theorem coe_restrictScalars' (f : M →L[A] M₂) : ⇑(f.restrictScalars R) = f :=
  rfl

@[simp]
theorem restrictScalars_zero : (0 : M →L[A] M₂).restrictScalars R = 0 :=
  rfl

section

variable [TopologicalAddGroup M₂]

@[simp]
theorem restrictScalars_add (f g : M →L[A] M₂) :
    (f + g).restrictScalars R = f.restrictScalars R + g.restrictScalars R :=
  rfl

@[simp]
theorem restrictScalars_neg (f : M →L[A] M₂) : (-f).restrictScalars R = -f.restrictScalars R :=
  rfl

end

variable {S : Type*}

variable [Ring S] [Module S M₂] [ContinuousConstSMul S M₂] [SMulCommClass A S M₂]
  [SMulCommClass R S M₂]

@[simp]
theorem restrictScalars_smul (c : S) (f : M →L[A] M₂) :
    (c • f).restrictScalars R = c • f.restrictScalars R :=
  rfl

variable (A M M₂ R S)

variable [TopologicalAddGroup M₂]

def restrictScalarsₗ : (M →L[A] M₂) →ₗ[S] M →L[R] M₂ where
  toFun := restrictScalars R
  map_add' := restrictScalars_add
  map_smul' := restrictScalars_smul

variable {A M M₂ R S}

@[simp]
theorem coe_restrictScalarsₗ : ⇑(restrictScalarsₗ A M M₂ R S) = restrictScalars R :=
  rfl

end RestrictScalars

end ContinuousLinearMap

namespace ContinuousLinearEquiv

section AddCommMonoid

variable {R₁ : Type*} {R₂ : Type*} {R₃ : Type*} [Semiring R₁] [Semiring R₂] [Semiring R₃]
  {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
  {σ₂₃ : R₂ →+* R₃} {σ₃₂ : R₃ →+* R₂} [RingHomInvPair σ₂₃ σ₃₂] [RingHomInvPair σ₃₂ σ₂₃]
  {σ₁₃ : R₁ →+* R₃} {σ₃₁ : R₃ →+* R₁} [RingHomInvPair σ₁₃ σ₃₁] [RingHomInvPair σ₃₁ σ₁₃]
  [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomCompTriple σ₃₂ σ₂₁ σ₃₁] {M₁ : Type*}
  [TopologicalSpace M₁] [AddCommMonoid M₁]
  {M₂ : Type*} [TopologicalSpace M₂] [AddCommMonoid M₂] {M₃ : Type*} [TopologicalSpace M₃]
  [AddCommMonoid M₃] {M₄ : Type*} [TopologicalSpace M₄] [AddCommMonoid M₄] [Module R₁ M₁]
  [Module R₂ M₂] [Module R₃ M₃]

@[coe]
def toContinuousLinearMap (e : M₁ ≃SL[σ₁₂] M₂) : M₁ →SL[σ₁₂] M₂ :=
  { e.toLinearEquiv.toLinearMap with cont := e.continuous_toFun }

instance ContinuousLinearMap.coe : Coe (M₁ ≃SL[σ₁₂] M₂) (M₁ →SL[σ₁₂] M₂) :=
  ⟨toContinuousLinearMap⟩

instance equivLike :
    EquivLike (M₁ ≃SL[σ₁₂] M₂) M₁ M₂ where
  coe f := f.toFun
  inv f := f.invFun
  coe_injective' f g h₁ h₂ := by
    cases' f with f' _
    cases' g with g' _
    rcases f' with ⟨⟨⟨_, _⟩, _⟩, _⟩
    rcases g' with ⟨⟨⟨_, _⟩, _⟩, _⟩
    congr
  left_inv f := f.left_inv
  right_inv f := f.right_inv

instance continuousSemilinearEquivClass :
    ContinuousSemilinearEquivClass (M₁ ≃SL[σ₁₂] M₂) σ₁₂ M₁ M₂ where
  map_add f := f.map_add'
  map_smulₛₗ f := f.map_smul'
  map_continuous := continuous_toFun
  inv_continuous := continuous_invFun

theorem coe_apply (e : M₁ ≃SL[σ₁₂] M₂) (b : M₁) : (e : M₁ →SL[σ₁₂] M₂) b = e b :=
  rfl

@[simp]
theorem coe_toLinearEquiv (f : M₁ ≃SL[σ₁₂] M₂) : ⇑f.toLinearEquiv = f :=
  rfl

@[simp, norm_cast]
theorem coe_coe (e : M₁ ≃SL[σ₁₂] M₂) : ⇑(e : M₁ →SL[σ₁₂] M₂) = e :=
  rfl

theorem toLinearEquiv_injective :
    Function.Injective (toLinearEquiv : (M₁ ≃SL[σ₁₂] M₂) → M₁ ≃ₛₗ[σ₁₂] M₂) := by
  rintro ⟨e, _, _⟩ ⟨e', _, _⟩ rfl
  rfl

@[ext]
theorem ext {f g : M₁ ≃SL[σ₁₂] M₂} (h : (f : M₁ → M₂) = g) : f = g :=
  toLinearEquiv_injective <| LinearEquiv.ext <| congr_fun h

theorem coe_injective : Function.Injective ((↑) : (M₁ ≃SL[σ₁₂] M₂) → M₁ →SL[σ₁₂] M₂) :=
  fun _e _e' h => ext <| funext <| ContinuousLinearMap.ext_iff.1 h

@[simp, norm_cast]
theorem coe_inj {e e' : M₁ ≃SL[σ₁₂] M₂} : (e : M₁ →SL[σ₁₂] M₂) = e' ↔ e = e' :=
  coe_injective.eq_iff

def toHomeomorph (e : M₁ ≃SL[σ₁₂] M₂) : M₁ ≃ₜ M₂ :=
  { e with toEquiv := e.toLinearEquiv.toEquiv }

@[simp]
theorem coe_toHomeomorph (e : M₁ ≃SL[σ₁₂] M₂) : ⇑e.toHomeomorph = e :=
  rfl

theorem isOpenMap (e : M₁ ≃SL[σ₁₂] M₂) : IsOpenMap e :=
  (ContinuousLinearEquiv.toHomeomorph e).isOpenMap

theorem image_closure (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₁) : e '' closure s = closure (e '' s) :=
  e.toHomeomorph.image_closure s

theorem preimage_closure (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₂) : e ⁻¹' closure s = closure (e ⁻¹' s) :=
  e.toHomeomorph.preimage_closure s

@[simp]
theorem isClosed_image (e : M₁ ≃SL[σ₁₂] M₂) {s : Set M₁} : IsClosed (e '' s) ↔ IsClosed s :=
  e.toHomeomorph.isClosed_image

theorem map_nhds_eq (e : M₁ ≃SL[σ₁₂] M₂) (x : M₁) : map e (𝓝 x) = 𝓝 (e x) :=
  e.toHomeomorph.map_nhds_eq x

theorem map_zero (e : M₁ ≃SL[σ₁₂] M₂) : e (0 : M₁) = 0 :=
  (e : M₁ →SL[σ₁₂] M₂).map_zero

theorem map_add (e : M₁ ≃SL[σ₁₂] M₂) (x y : M₁) : e (x + y) = e x + e y :=
  (e : M₁ →SL[σ₁₂] M₂).map_add x y

@[simp]
theorem map_smulₛₗ (e : M₁ ≃SL[σ₁₂] M₂) (c : R₁) (x : M₁) : e (c • x) = σ₁₂ c • e x :=
  (e : M₁ →SL[σ₁₂] M₂).map_smulₛₗ c x

theorem map_smul [Module R₁ M₂] (e : M₁ ≃L[R₁] M₂) (c : R₁) (x : M₁) : e (c • x) = c • e x :=
  (e : M₁ →L[R₁] M₂).map_smul c x

theorem map_eq_zero_iff (e : M₁ ≃SL[σ₁₂] M₂) {x : M₁} : e x = 0 ↔ x = 0 :=
  e.toLinearEquiv.map_eq_zero_iff

attribute [continuity]
  ContinuousLinearEquiv.continuous_toFun ContinuousLinearEquiv.continuous_invFun

@[continuity]
protected theorem continuous (e : M₁ ≃SL[σ₁₂] M₂) : Continuous (e : M₁ → M₂) :=
  e.continuous_toFun

protected theorem continuousOn (e : M₁ ≃SL[σ₁₂] M₂) {s : Set M₁} : ContinuousOn (e : M₁ → M₂) s :=
  e.continuous.continuousOn

protected theorem continuousAt (e : M₁ ≃SL[σ₁₂] M₂) {x : M₁} : ContinuousAt (e : M₁ → M₂) x :=
  e.continuous.continuousAt

protected theorem continuousWithinAt (e : M₁ ≃SL[σ₁₂] M₂) {s : Set M₁} {x : M₁} :
    ContinuousWithinAt (e : M₁ → M₂) s x :=
  e.continuous.continuousWithinAt

theorem comp_continuousOn_iff {α : Type*} [TopologicalSpace α] (e : M₁ ≃SL[σ₁₂] M₂) {f : α → M₁}
    {s : Set α} : ContinuousOn (e ∘ f) s ↔ ContinuousOn f s :=
  e.toHomeomorph.comp_continuousOn_iff _ _

theorem comp_continuous_iff {α : Type*} [TopologicalSpace α] (e : M₁ ≃SL[σ₁₂] M₂) {f : α → M₁} :
    Continuous (e ∘ f) ↔ Continuous f :=
  e.toHomeomorph.comp_continuous_iff

theorem ext₁ [TopologicalSpace R₁] {f g : R₁ ≃L[R₁] M₁} (h : f 1 = g 1) : f = g :=
  ext <| funext fun x => mul_one x ▸ by rw [← smul_eq_mul, map_smul, h, map_smul]

section

variable (R₁ M₁)

@[refl]
protected def refl : M₁ ≃L[R₁] M₁ :=
  { LinearEquiv.refl R₁ M₁ with
    continuous_toFun := continuous_id
    continuous_invFun := continuous_id }

@[simp]
theorem refl_apply (x : M₁) :
    ContinuousLinearEquiv.refl R₁ M₁ x = x := rfl

end

@[simp, norm_cast]
theorem coe_refl : ↑(ContinuousLinearEquiv.refl R₁ M₁) = ContinuousLinearMap.id R₁ M₁ :=
  rfl

@[simp, norm_cast]
theorem coe_refl' : ⇑(ContinuousLinearEquiv.refl R₁ M₁) = id :=
  rfl

@[symm]
protected def symm (e : M₁ ≃SL[σ₁₂] M₂) : M₂ ≃SL[σ₂₁] M₁ :=
  { e.toLinearEquiv.symm with
    continuous_toFun := e.continuous_invFun
    continuous_invFun := e.continuous_toFun }

@[simp]
theorem symm_toLinearEquiv (e : M₁ ≃SL[σ₁₂] M₂) : e.symm.toLinearEquiv = e.toLinearEquiv.symm := by
  ext
  rfl

@[simp]
theorem symm_toHomeomorph (e : M₁ ≃SL[σ₁₂] M₂) : e.toHomeomorph.symm = e.symm.toHomeomorph :=
  rfl

def Simps.apply (h : M₁ ≃SL[σ₁₂] M₂) : M₁ → M₂ :=
  h

def Simps.symm_apply (h : M₁ ≃SL[σ₁₂] M₂) : M₂ → M₁ :=
  h.symm

initialize_simps_projections ContinuousLinearEquiv (toFun → apply, invFun → symm_apply)

theorem symm_map_nhds_eq (e : M₁ ≃SL[σ₁₂] M₂) (x : M₁) : map e.symm (𝓝 (e x)) = 𝓝 x :=
  e.toHomeomorph.symm_map_nhds_eq x

@[trans]
protected def trans (e₁ : M₁ ≃SL[σ₁₂] M₂) (e₂ : M₂ ≃SL[σ₂₃] M₃) : M₁ ≃SL[σ₁₃] M₃ :=
  { e₁.toLinearEquiv.trans e₂.toLinearEquiv with
    continuous_toFun := e₂.continuous_toFun.comp e₁.continuous_toFun
    continuous_invFun := e₁.continuous_invFun.comp e₂.continuous_invFun }

@[simp]
theorem trans_toLinearEquiv (e₁ : M₁ ≃SL[σ₁₂] M₂) (e₂ : M₂ ≃SL[σ₂₃] M₃) :
    (e₁.trans e₂).toLinearEquiv = e₁.toLinearEquiv.trans e₂.toLinearEquiv := by
  ext
  rfl

def prod [Module R₁ M₂] [Module R₁ M₃] [Module R₁ M₄] (e : M₁ ≃L[R₁] M₂) (e' : M₃ ≃L[R₁] M₄) :
    (M₁ × M₃) ≃L[R₁] M₂ × M₄ :=
  { e.toLinearEquiv.prod e'.toLinearEquiv with
    continuous_toFun := e.continuous_toFun.prodMap e'.continuous_toFun
    continuous_invFun := e.continuous_invFun.prodMap e'.continuous_invFun }

@[simp, norm_cast]
theorem prod_apply [Module R₁ M₂] [Module R₁ M₃] [Module R₁ M₄] (e : M₁ ≃L[R₁] M₂)
    (e' : M₃ ≃L[R₁] M₄) (x) : e.prod e' x = (e x.1, e' x.2) :=
  rfl

@[simp, norm_cast]
theorem coe_prod [Module R₁ M₂] [Module R₁ M₃] [Module R₁ M₄] (e : M₁ ≃L[R₁] M₂)
    (e' : M₃ ≃L[R₁] M₄) :
    (e.prod e' : M₁ × M₃ →L[R₁] M₂ × M₄) = (e : M₁ →L[R₁] M₂).prodMap (e' : M₃ →L[R₁] M₄) :=
  rfl

theorem prod_symm [Module R₁ M₂] [Module R₁ M₃] [Module R₁ M₄] (e : M₁ ≃L[R₁] M₂)
    (e' : M₃ ≃L[R₁] M₄) : (e.prod e').symm = e.symm.prod e'.symm :=
  rfl

variable (R₁ M₁ M₂)

@[simps! apply toLinearEquiv]
def prodComm [Module R₁ M₂] : (M₁ × M₂) ≃L[R₁] M₂ × M₁ :=
  { LinearEquiv.prodComm R₁ M₁ M₂ with
    continuous_toFun := continuous_swap
    continuous_invFun := continuous_swap }

@[simp] lemma prodComm_symm [Module R₁ M₂] : (prodComm R₁ M₁ M₂).symm = prodComm R₁ M₂ M₁ := rfl

variable {R₁ M₁ M₂}

protected theorem bijective (e : M₁ ≃SL[σ₁₂] M₂) : Function.Bijective e :=
  e.toLinearEquiv.toEquiv.bijective

protected theorem injective (e : M₁ ≃SL[σ₁₂] M₂) : Function.Injective e :=
  e.toLinearEquiv.toEquiv.injective

protected theorem surjective (e : M₁ ≃SL[σ₁₂] M₂) : Function.Surjective e :=
  e.toLinearEquiv.toEquiv.surjective

@[simp]
theorem trans_apply (e₁ : M₁ ≃SL[σ₁₂] M₂) (e₂ : M₂ ≃SL[σ₂₃] M₃) (c : M₁) :
    (e₁.trans e₂) c = e₂ (e₁ c) :=
  rfl

@[simp]
theorem apply_symm_apply (e : M₁ ≃SL[σ₁₂] M₂) (c : M₂) : e (e.symm c) = c :=
  e.1.right_inv c

@[simp]
theorem symm_apply_apply (e : M₁ ≃SL[σ₁₂] M₂) (b : M₁) : e.symm (e b) = b :=
  e.1.left_inv b

@[simp]
theorem symm_trans_apply (e₁ : M₂ ≃SL[σ₂₁] M₁) (e₂ : M₃ ≃SL[σ₃₂] M₂) (c : M₁) :
    (e₂.trans e₁).symm c = e₂.symm (e₁.symm c) :=
  rfl

@[simp]
theorem symm_image_image (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₁) : e.symm '' (e '' s) = s :=
  e.toLinearEquiv.toEquiv.symm_image_image s

@[simp]
theorem image_symm_image (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₂) : e '' (e.symm '' s) = s :=
  e.symm.symm_image_image s

@[simp, norm_cast]
theorem comp_coe (f : M₁ ≃SL[σ₁₂] M₂) (f' : M₂ ≃SL[σ₂₃] M₃) :
    (f' : M₂ →SL[σ₂₃] M₃).comp (f : M₁ →SL[σ₁₂] M₂) = (f.trans f' : M₁ →SL[σ₁₃] M₃) :=
  rfl

@[simp high]
theorem coe_comp_coe_symm (e : M₁ ≃SL[σ₁₂] M₂) :
    (e : M₁ →SL[σ₁₂] M₂).comp (e.symm : M₂ →SL[σ₂₁] M₁) = ContinuousLinearMap.id R₂ M₂ :=
  ContinuousLinearMap.ext e.apply_symm_apply

@[simp high]
theorem coe_symm_comp_coe (e : M₁ ≃SL[σ₁₂] M₂) :
    (e.symm : M₂ →SL[σ₂₁] M₁).comp (e : M₁ →SL[σ₁₂] M₂) = ContinuousLinearMap.id R₁ M₁ :=
  ContinuousLinearMap.ext e.symm_apply_apply

@[simp]
theorem symm_comp_self (e : M₁ ≃SL[σ₁₂] M₂) : (e.symm : M₂ → M₁) ∘ (e : M₁ → M₂) = id := by
  ext x
  exact symm_apply_apply e x

@[simp]
theorem self_comp_symm (e : M₁ ≃SL[σ₁₂] M₂) : (e : M₁ → M₂) ∘ (e.symm : M₂ → M₁) = id := by
  ext x
  exact apply_symm_apply e x

@[simp]
theorem symm_symm (e : M₁ ≃SL[σ₁₂] M₂) : e.symm.symm = e := rfl

@[simp]
theorem refl_symm : (ContinuousLinearEquiv.refl R₁ M₁).symm = ContinuousLinearEquiv.refl R₁ M₁ :=
  rfl

theorem symm_symm_apply (e : M₁ ≃SL[σ₁₂] M₂) (x : M₁) : e.symm.symm x = e x :=
  rfl

theorem symm_apply_eq (e : M₁ ≃SL[σ₁₂] M₂) {x y} : e.symm x = y ↔ x = e y :=
  e.toLinearEquiv.symm_apply_eq

theorem eq_symm_apply (e : M₁ ≃SL[σ₁₂] M₂) {x y} : y = e.symm x ↔ e y = x :=
  e.toLinearEquiv.eq_symm_apply

protected theorem image_eq_preimage (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₁) : e '' s = e.symm ⁻¹' s :=
  e.toLinearEquiv.toEquiv.image_eq_preimage s

protected theorem image_symm_eq_preimage (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₂) :
    e.symm '' s = e ⁻¹' s := by rw [e.symm.image_eq_preimage, e.symm_symm]

@[simp]
protected theorem symm_preimage_preimage (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₂) :
    e.symm ⁻¹' (e ⁻¹' s) = s :=
  e.toLinearEquiv.toEquiv.symm_preimage_preimage s

@[simp]
protected theorem preimage_symm_preimage (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₁) :
    e ⁻¹' (e.symm ⁻¹' s) = s :=
  e.symm.symm_preimage_preimage s

lemma isUniformEmbedding {E₁ E₂ : Type*} [UniformSpace E₁] [UniformSpace E₂]
    [AddCommGroup E₁] [AddCommGroup E₂] [Module R₁ E₁] [Module R₂ E₂] [UniformAddGroup E₁]
    [UniformAddGroup E₂] (e : E₁ ≃SL[σ₁₂] E₂) : IsUniformEmbedding e :=
  e.toLinearEquiv.toEquiv.isUniformEmbedding e.toContinuousLinearMap.uniformContinuous
    e.symm.toContinuousLinearMap.uniformContinuous

protected theorem _root_.LinearEquiv.isUniformEmbedding {E₁ E₂ : Type*} [UniformSpace E₁]
    [UniformSpace E₂] [AddCommGroup E₁] [AddCommGroup E₂] [Module R₁ E₁] [Module R₂ E₂]
    [UniformAddGroup E₁] [UniformAddGroup E₂] (e : E₁ ≃ₛₗ[σ₁₂] E₂)
    (h₁ : Continuous e) (h₂ : Continuous e.symm) : IsUniformEmbedding e :=
  ContinuousLinearEquiv.isUniformEmbedding
    ({ e with
        continuous_toFun := h₁
        continuous_invFun := h₂ } :
      E₁ ≃SL[σ₁₂] E₂)

alias _root_.LinearEquiv.uniformEmbedding := _root_.LinearEquiv.isUniformEmbedding

def equivOfInverse (f₁ : M₁ →SL[σ₁₂] M₂) (f₂ : M₂ →SL[σ₂₁] M₁) (h₁ : Function.LeftInverse f₂ f₁)
    (h₂ : Function.RightInverse f₂ f₁) : M₁ ≃SL[σ₁₂] M₂ :=
  { f₁ with
    continuous_toFun := f₁.continuous
    invFun := f₂
    continuous_invFun := f₂.continuous
    left_inv := h₁
    right_inv := h₂ }

@[simp]
theorem equivOfInverse_apply (f₁ : M₁ →SL[σ₁₂] M₂) (f₂ h₁ h₂ x) :
    equivOfInverse f₁ f₂ h₁ h₂ x = f₁ x :=
  rfl

@[simp]
theorem symm_equivOfInverse (f₁ : M₁ →SL[σ₁₂] M₂) (f₂ h₁ h₂) :
    (equivOfInverse f₁ f₂ h₁ h₂).symm = equivOfInverse f₂ f₁ h₂ h₁ :=
  rfl

def equivOfInverse' (f₁ : M₁ →SL[σ₁₂] M₂) (f₂ : M₂ →SL[σ₂₁] M₁)
    (h₁ : f₁.comp f₂ = .id R₂ M₂) (h₂ : f₂.comp f₁ = .id R₁ M₁) : M₁ ≃SL[σ₁₂] M₂ :=
  equivOfInverse f₁ f₂
    (fun x ↦ by simpa using congr($(h₂) x)) (fun x ↦ by simpa using congr($(h₁) x))

@[simp]
theorem equivOfInverse'_apply (f₁ : M₁ →SL[σ₁₂] M₂) (f₂ h₁ h₂ x) :
    equivOfInverse' f₁ f₂ h₁ h₂ x = f₁ x :=
  rfl

@[simp]
theorem symm_equivOfInverse' (f₁ : M₁ →SL[σ₁₂] M₂) (f₂ h₁ h₂) :
    (equivOfInverse' f₁ f₂ h₁ h₂).symm = equivOfInverse' f₂ f₁ h₂ h₁ :=
  rfl

variable (M₁)

instance automorphismGroup : Group (M₁ ≃L[R₁] M₁) where
  mul f g := g.trans f
  one := ContinuousLinearEquiv.refl R₁ M₁
  inv f := f.symm
  mul_assoc f g h := by
    ext
    rfl
  mul_one f := by
    ext
    rfl
  one_mul f := by
    ext
    rfl
  inv_mul_cancel f := by
    ext x
    exact f.left_inv x

variable {M₁} {R₄ : Type*} [Semiring R₄] [Module R₄ M₄] {σ₃₄ : R₃ →+* R₄} {σ₄₃ : R₄ →+* R₃}
  [RingHomInvPair σ₃₄ σ₄₃] [RingHomInvPair σ₄₃ σ₃₄] {σ₂₄ : R₂ →+* R₄} {σ₁₄ : R₁ →+* R₄}
  [RingHomCompTriple σ₂₁ σ₁₄ σ₂₄] [RingHomCompTriple σ₂₄ σ₄₃ σ₂₃] [RingHomCompTriple σ₁₃ σ₃₄ σ₁₄]

def ulift : ULift M₁ ≃L[R₁] M₁ :=
  { ULift.moduleEquiv with
    continuous_toFun := continuous_uLift_down
    continuous_invFun := continuous_uLift_up }

@[simps]
def arrowCongrEquiv (e₁₂ : M₁ ≃SL[σ₁₂] M₂) (e₄₃ : M₄ ≃SL[σ₄₃] M₃) :
    (M₁ →SL[σ₁₄] M₄) ≃ (M₂ →SL[σ₂₃] M₃) where
  toFun f := (e₄₃ : M₄ →SL[σ₄₃] M₃).comp (f.comp (e₁₂.symm : M₂ →SL[σ₂₁] M₁))
  invFun f := (e₄₃.symm : M₃ →SL[σ₃₄] M₄).comp (f.comp (e₁₂ : M₁ →SL[σ₁₂] M₂))
  left_inv f :=
    ContinuousLinearMap.ext fun x => by
      simp only [ContinuousLinearMap.comp_apply, symm_apply_apply, coe_coe]
  right_inv f :=
    ContinuousLinearMap.ext fun x => by
      simp only [ContinuousLinearMap.comp_apply, apply_symm_apply, coe_coe]

section piCongrRight

variable {ι : Type*} {M : ι → Type*} [∀ i, TopologicalSpace (M i)] [∀ i, AddCommMonoid (M i)]
  [∀ i, Module R₁ (M i)] {N : ι → Type*} [∀ i, TopologicalSpace (N i)] [∀ i, AddCommMonoid (N i)]
  [∀ i, Module R₁ (N i)] (f : (i : ι) → M i ≃L[R₁] N i)

def piCongrRight : ((i : ι) → M i) ≃L[R₁] (i : ι) → N i :=
  { LinearEquiv.piCongrRight fun i ↦ f i with
    continuous_toFun := by
      exact continuous_pi fun i ↦ (f i).continuous_toFun.comp (continuous_apply i)
    continuous_invFun := by
      exact continuous_pi fun i => (f i).continuous_invFun.comp (continuous_apply i) }

@[simp]
theorem piCongrRight_apply (m : (i : ι) → M i) (i : ι) :
    piCongrRight f m i = (f i) (m i) := rfl

@[simp]
theorem piCongrRight_symm_apply (n : (i : ι) → N i) (i : ι) :
    (piCongrRight f).symm n i = (f i).symm (n i) := rfl

end piCongrRight

end AddCommMonoid

section AddCommGroup

variable {R : Type*} [Semiring R] {M : Type*} [TopologicalSpace M] [AddCommGroup M] {M₂ : Type*}
  [TopologicalSpace M₂] [AddCommGroup M₂] {M₃ : Type*} [TopologicalSpace M₃] [AddCommGroup M₃]
  {M₄ : Type*} [TopologicalSpace M₄] [AddCommGroup M₄] [Module R M] [Module R M₂] [Module R M₃]
  [Module R M₄]

variable [TopologicalAddGroup M₄]

def skewProd (e : M ≃L[R] M₂) (e' : M₃ ≃L[R] M₄) (f : M →L[R] M₄) : (M × M₃) ≃L[R] M₂ × M₄ :=
  {
    e.toLinearEquiv.skewProd e'.toLinearEquiv
      ↑f with
    continuous_toFun :=
      (e.continuous_toFun.comp continuous_fst).prod_mk
        ((e'.continuous_toFun.comp continuous_snd).add <| f.continuous.comp continuous_fst)
    continuous_invFun :=
      (e.continuous_invFun.comp continuous_fst).prod_mk
        (e'.continuous_invFun.comp <|
          continuous_snd.sub <| f.continuous.comp <| e.continuous_invFun.comp continuous_fst) }

@[simp]
theorem skewProd_apply (e : M ≃L[R] M₂) (e' : M₃ ≃L[R] M₄) (f : M →L[R] M₄) (x) :
    e.skewProd e' f x = (e x.1, e' x.2 + f x.1) :=
  rfl

@[simp]
theorem skewProd_symm_apply (e : M ≃L[R] M₂) (e' : M₃ ≃L[R] M₄) (f : M →L[R] M₄) (x) :
    (e.skewProd e' f).symm x = (e.symm x.1, e'.symm (x.2 - f (e.symm x.1))) :=
  rfl

variable (R) in

def neg [ContinuousNeg M] :
    M ≃L[R] M :=
  { LinearEquiv.neg R with
    continuous_toFun := continuous_neg
    continuous_invFun := continuous_neg }

@[simp]
theorem coe_neg [ContinuousNeg M] :
    (neg R : M → M) = -id := rfl

@[simp]
theorem neg_apply [ContinuousNeg M] (x : M) :
    neg R x = -x := by simp

@[simp]
theorem symm_neg [ContinuousNeg M] :
    (neg R : M ≃L[R] M).symm = neg R := rfl

end AddCommGroup

section Ring

variable {R : Type*} [Ring R] {R₂ : Type*} [Ring R₂] {M : Type*} [TopologicalSpace M]
  [AddCommGroup M] [Module R M] {M₂ : Type*} [TopologicalSpace M₂] [AddCommGroup M₂] [Module R₂ M₂]

variable {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]

theorem map_sub (e : M ≃SL[σ₁₂] M₂) (x y : M) : e (x - y) = e x - e y :=
  (e : M →SL[σ₁₂] M₂).map_sub x y

theorem map_neg (e : M ≃SL[σ₁₂] M₂) (x : M) : e (-x) = -e x :=
  (e : M →SL[σ₁₂] M₂).map_neg x

section

/-! The next theorems cover the identification between `M ≃L[R] M`and the group of units of the ring
`M →L[R] M`. -/

def ofUnit (f : (M →L[R] M)ˣ) : M ≃L[R] M where
  toLinearEquiv :=
    { toFun := f.val
      map_add' := by simp
      map_smul' := by simp
      invFun := f.inv
      left_inv := fun x =>
        show (f.inv * f.val) x = x by
          rw [f.inv_val]
          simp
      right_inv := fun x =>
        show (f.val * f.inv) x = x by
          rw [f.val_inv]
          simp }
  continuous_toFun := f.val.continuous
  continuous_invFun := f.inv.continuous

def toUnit (f : M ≃L[R] M) : (M →L[R] M)ˣ where
  val := f
  inv := f.symm
  val_inv := by
    ext
    simp
  inv_val := by
    ext
    simp

variable (R M)

def unitsEquiv : (M →L[R] M)ˣ ≃* M ≃L[R] M where
  toFun := ofUnit
  invFun := toUnit
  left_inv f := by
    ext
    rfl
  right_inv f := by
    ext
    rfl
  map_mul' x y := by
    ext
    rfl

@[simp]
theorem unitsEquiv_apply (f : (M →L[R] M)ˣ) (x : M) : unitsEquiv R M f x = (f : M →L[R] M) x :=
  rfl

end

section

variable (R) [TopologicalSpace R]

variable [ContinuousMul R]

def unitsEquivAut : Rˣ ≃ R ≃L[R] R where
  toFun u :=
    equivOfInverse (ContinuousLinearMap.smulRight (1 : R →L[R] R) ↑u)
      (ContinuousLinearMap.smulRight (1 : R →L[R] R) ↑u⁻¹) (fun x => by simp) fun x => by simp
  invFun e :=
    ⟨e 1, e.symm 1, by rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one, symm_apply_apply], by
      rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one, apply_symm_apply]⟩
  left_inv u := Units.ext <| by simp
  right_inv e := ext₁ <| by simp

variable {R}

@[simp]
theorem unitsEquivAut_apply (u : Rˣ) (x : R) : unitsEquivAut R u x = x * u :=
  rfl

@[simp]
theorem unitsEquivAut_apply_symm (u : Rˣ) (x : R) : (unitsEquivAut R u).symm x = x * ↑u⁻¹ :=
  rfl

@[simp]
theorem unitsEquivAut_symm_apply (e : R ≃L[R] R) : ↑((unitsEquivAut R).symm e) = e 1 :=
  rfl

end

variable [Module R M₂] [TopologicalAddGroup M]

def equivOfRightInverse (f₁ : M →L[R] M₂) (f₂ : M₂ →L[R] M) (h : Function.RightInverse f₂ f₁) :
    M ≃L[R] M₂ × ker f₁ :=
  equivOfInverse (f₁.prod (f₁.projKerOfRightInverse f₂ h)) (f₂.coprod (ker f₁).subtypeL)
    (fun x => by simp) fun ⟨x, y⟩ => by
      -- Porting note: `simp` timeouts.
      rw [ContinuousLinearMap.coprod_apply,
        Submodule.subtypeL_apply, _root_.map_add, ContinuousLinearMap.prod_apply, h x,
        ContinuousLinearMap.projKerOfRightInverse_comp_inv,
        ContinuousLinearMap.prod_apply, LinearMap.map_coe_ker,
        ContinuousLinearMap.projKerOfRightInverse_apply_idem, Prod.mk_add_mk, add_zero, zero_add]

@[simp]
theorem fst_equivOfRightInverse (f₁ : M →L[R] M₂) (f₂ : M₂ →L[R] M)
    (h : Function.RightInverse f₂ f₁) (x : M) : (equivOfRightInverse f₁ f₂ h x).1 = f₁ x :=
  rfl

@[simp]
theorem snd_equivOfRightInverse (f₁ : M →L[R] M₂) (f₂ : M₂ →L[R] M)
    (h : Function.RightInverse f₂ f₁) (x : M) :
    ((equivOfRightInverse f₁ f₂ h x).2 : M) = x - f₂ (f₁ x) :=
  rfl

@[simp]
theorem equivOfRightInverse_symm_apply (f₁ : M →L[R] M₂) (f₂ : M₂ →L[R] M)
    (h : Function.RightInverse f₂ f₁) (y : M₂ × ker f₁) :
    (equivOfRightInverse f₁ f₂ h).symm y = f₂ y.1 + y.2 :=
  rfl

end Ring

section

variable (ι R M : Type*) [Unique ι] [Semiring R] [AddCommMonoid M] [Module R M]
  [TopologicalSpace M]

def funUnique : (ι → M) ≃L[R] M :=
  { Homeomorph.funUnique ι M with toLinearEquiv := LinearEquiv.funUnique ι R M }

variable {ι R M}

@[simp]
theorem coe_funUnique : ⇑(funUnique ι R M) = Function.eval default :=
  rfl

@[simp]
theorem coe_funUnique_symm : ⇑(funUnique ι R M).symm = Function.const ι :=
  rfl

variable (R M)

@[simps! (config := .asFn) apply symm_apply]
def piFinTwo (M : Fin 2 → Type*) [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    [∀ i, TopologicalSpace (M i)] : ((i : _) → M i) ≃L[R] M 0 × M 1 :=
  { Homeomorph.piFinTwo M with toLinearEquiv := LinearEquiv.piFinTwo R M }

@[simps! (config := .asFn) apply symm_apply]
def finTwoArrow : (Fin 2 → M) ≃L[R] M × M :=
  { piFinTwo R fun _ => M with toLinearEquiv := LinearEquiv.finTwoArrow R M }

end

end ContinuousLinearEquiv

namespace ContinuousLinearMap

variable {R : Type*} {M M₂ M₃ : Type*}
  [TopologicalSpace M] [TopologicalSpace M₂] [TopologicalSpace M₃]

section

variable [Semiring R]
  [AddCommMonoid M] [Module R M]
  [AddCommMonoid M₂] [Module R M₂]
  [AddCommMonoid M₃] [Module R M₃]

def IsInvertible (f : M →L[R] M₂) : Prop :=
  ∃ (A : M ≃L[R] M₂), A = f

open Classical in

noncomputable def inverse : (M →L[R] M₂) → M₂ →L[R] M := fun f =>
  if h : f.IsInvertible then ((Classical.choose h).symm : M₂ →L[R] M) else 0

@[simp] lemma isInvertible_equiv {f : M ≃L[R] M₂} : IsInvertible (f : M →L[R] M₂) := ⟨f, rfl⟩

@[simp]
theorem inverse_equiv (e : M ≃L[R] M₂) : inverse (e : M →L[R] M₂) = e.symm := by
  simp [inverse]

@[simp] lemma inverse_of_not_isInvertible
    {f : M →L[R] M₂} (hf : ¬ f.IsInvertible) : f.inverse = 0 :=
  dif_neg hf

@[simp] theorem inverse_zero : inverse (0 : M →L[R] M₂) = 0 := by
  by_cases h : IsInvertible (0 : M →L[R] M₂)
  · rcases h with ⟨e', he'⟩
    simp only [← he', inverse_equiv]
    ext v
    apply e'.injective
    rw [← ContinuousLinearEquiv.coe_coe, he']
    rfl
  · exact inverse_of_not_isInvertible h

lemma IsInvertible.comp {g : M₂ →L[R] M₃} {f : M →L[R] M₂}
    (hg : g.IsInvertible) (hf : f.IsInvertible) : (g ∘L f).IsInvertible := by
  rcases hg with ⟨N, rfl⟩
  rcases hf with ⟨M, rfl⟩
  exact ⟨M.trans N, rfl⟩

lemma IsInvertible.of_inverse {f : M →L[R] M₂} {g : M₂ →L[R] M}
    (hf : f ∘L g = id R M₂) (hg : g ∘L f = id R M) :
    f.IsInvertible :=
  ⟨ContinuousLinearEquiv.equivOfInverse' _ _ hf hg, rfl⟩

lemma inverse_eq {f : M →L[R] M₂} {g : M₂ →L[R] M} (hf : f ∘L g = id R M₂) (hg : g ∘L f = id R M) :
    f.inverse = g := by
  have : f = ContinuousLinearEquiv.equivOfInverse' f g hf hg := rfl
  rw [this, inverse_equiv]
  rfl

lemma IsInvertible.inverse_apply_eq {f : M →L[R] M₂} {x : M} {y : M₂} (hf : f.IsInvertible) :
    f.inverse y = x ↔ y = f x := by
  rcases hf with ⟨M, rfl⟩
  simp only [inverse_equiv, ContinuousLinearEquiv.coe_coe]
  exact ContinuousLinearEquiv.symm_apply_eq M

@[simp] lemma isInvertible_equiv_comp {e : M₂ ≃L[R] M₃} {f : M →L[R] M₂} :
    ((e : M₂ →L[R] M₃) ∘L f).IsInvertible ↔ f.IsInvertible := by
  constructor
  · rintro ⟨A, hA⟩
    have : f = e.symm ∘L ((e : M₂ →L[R] M₃) ∘L f) := by ext; simp
    rw [this, ← hA]
    simp
  · rintro ⟨M, rfl⟩
    simp

@[simp] lemma isInvertible_comp_equiv {e : M₃ ≃L[R] M} {f : M →L[R] M₂} :
    (f ∘L (e : M₃ →L[R] M)).IsInvertible ↔ f.IsInvertible := by
  constructor
  · rintro ⟨A, hA⟩
    have : f = (f ∘L (e : M₃ →L[R] M)) ∘L e.symm := by ext; simp
    rw [this, ← hA]
    simp
  · rintro ⟨M, rfl⟩
    simp

@[simp] lemma inverse_equiv_comp {e : M₂ ≃L[R] M₃} {f : M →L[R] M₂} :
    (e ∘L f).inverse = f.inverse ∘L (e.symm : M₃ →L[R] M₂) := by
  by_cases hf : f.IsInvertible
  · rcases hf with ⟨A, rfl⟩
    simp only [ContinuousLinearEquiv.comp_coe, inverse_equiv, ContinuousLinearEquiv.coe_inj]
    rfl
  · rw [inverse_of_not_isInvertible (by simp [hf]), inverse_of_not_isInvertible hf]
    rfl

@[simp] lemma inverse_comp_equiv {e : M₃ ≃L[R] M} {f : M →L[R] M₂} :
    (f ∘L e).inverse = (e.symm : M →L[R] M₃) ∘L f.inverse := by
  by_cases hf : f.IsInvertible
  · rcases hf with ⟨A, rfl⟩
    simp only [ContinuousLinearEquiv.comp_coe, inverse_equiv, ContinuousLinearEquiv.coe_inj]
    rfl
  · rw [inverse_of_not_isInvertible (by simp [hf]), inverse_of_not_isInvertible hf]
    simp

lemma IsInvertible.inverse_comp_of_left {g : M₂ →L[R] M₃} {f : M →L[R] M₂}
    (hg : g.IsInvertible) : (g ∘L f).inverse = f.inverse ∘L g.inverse := by
  rcases hg with ⟨N, rfl⟩
  simp

lemma IsInvertible.inverse_comp_apply_of_left {g : M₂ →L[R] M₃} {f : M →L[R] M₂} {v : M₃}
    (hg : g.IsInvertible) : (g ∘L f).inverse v = f.inverse (g.inverse v) := by
  simp only [hg.inverse_comp_of_left, coe_comp', Function.comp_apply]

lemma IsInvertible.inverse_comp_of_right {g : M₂ →L[R] M₃} {f : M →L[R] M₂}
    (hf : f.IsInvertible) : (g ∘L f).inverse = f.inverse ∘L g.inverse := by
  rcases hf with ⟨M, rfl⟩
  simp

lemma IsInvertible.inverse_comp_apply_of_right {g : M₂ →L[R] M₃} {f : M →L[R] M₂} {v : M₃}
    (hf : f.IsInvertible) : (g ∘L f).inverse v = f.inverse (g.inverse v) := by
  simp only [hf.inverse_comp_of_right, coe_comp', Function.comp_apply]

end

section

variable [Ring R]

variable [AddCommGroup M] [Module R M]

variable [AddCommGroup M₂] [Module R M₂]

@[simp]
theorem ring_inverse_equiv (e : M ≃L[R] M) : Ring.inverse ↑e = inverse (e : M →L[R] M) := by
  suffices Ring.inverse ((ContinuousLinearEquiv.unitsEquiv _ _).symm e : M →L[R] M) = inverse ↑e by
    convert this
  simp
  rfl

theorem to_ring_inverse (e : M ≃L[R] M₂) (f : M →L[R] M₂) :
    inverse f = Ring.inverse ((e.symm : M₂ →L[R] M).comp f) ∘L e.symm := by
  by_cases h₁ : f.IsInvertible
  · obtain ⟨e', he'⟩ := h₁
    rw [← he']
    change _ = Ring.inverse (e'.trans e.symm : M →L[R] M) ∘L (e.symm : M₂ →L[R] M)
    ext
    simp
  · suffices ¬IsUnit ((e.symm : M₂ →L[R] M).comp f) by simp [this, h₁]
    contrapose! h₁
    rcases h₁ with ⟨F, hF⟩
    use (ContinuousLinearEquiv.unitsEquiv _ _ F).trans e
    ext
    dsimp
    rw [hF]
    simp

theorem ring_inverse_eq_map_inverse : Ring.inverse = @inverse R M M _ _ _ _ _ _ _ := by
  ext
  simp [to_ring_inverse (ContinuousLinearEquiv.refl R M)]

@[simp] theorem inverse_id : (id R M).inverse = id R M := by
  rw [← ring_inverse_eq_map_inverse]
  exact Ring.inverse_one _

end

end ContinuousLinearMap

namespace Submodule

variable {R : Type*} [Ring R] {M : Type*} [TopologicalSpace M] [AddCommGroup M] [Module R M]

open ContinuousLinearMap

def ClosedComplemented (p : Submodule R M) : Prop :=
  ∃ f : M →L[R] p, ∀ x : p, f x = x

theorem ClosedComplemented.exists_isClosed_isCompl {p : Submodule R M} [T1Space p]
    (h : ClosedComplemented p) :
    ∃ q : Submodule R M, IsClosed (q : Set M) ∧ IsCompl p q :=
  Exists.elim h fun f hf => ⟨ker f, isClosed_ker f, LinearMap.isCompl_of_proj hf⟩

protected theorem ClosedComplemented.isClosed [TopologicalAddGroup M] [T1Space M]
    {p : Submodule R M} (h : ClosedComplemented p) : IsClosed (p : Set M) := by
  rcases h with ⟨f, hf⟩
  have : ker (id R M - p.subtypeL.comp f) = p := LinearMap.ker_id_sub_eq_of_proj hf
  exact this ▸ isClosed_ker _

@[simp]
theorem closedComplemented_bot : ClosedComplemented (⊥ : Submodule R M) :=
  ⟨0, fun x => by simp only [zero_apply, eq_zero_of_bot_submodule x]⟩

@[simp]
theorem closedComplemented_top : ClosedComplemented (⊤ : Submodule R M) :=
  ⟨(id R M).codRestrict ⊤ fun _x => trivial, fun x => Subtype.ext_iff_val.2 <| by simp⟩

lemma ClosedComplemented.exists_submodule_equiv_prod [TopologicalAddGroup M]
    {p : Submodule R M} (hp : p.ClosedComplemented) :
    ∃ (q : Submodule R M) (e : M ≃L[R] (p × q)),
      (∀ x : p, e x = (x, 0)) ∧ (∀ y : q, e y = (0, y)) ∧ (∀ x, e.symm x = x.1 + x.2) :=
  let ⟨f, hf⟩ := hp
  ⟨LinearMap.ker f, .equivOfRightInverse _ p.subtypeL hf,
    fun _ ↦ by ext <;> simp [hf], fun _ ↦ by ext <;> simp [hf], fun _ ↦ rfl⟩

end Submodule

theorem ContinuousLinearMap.closedComplemented_ker_of_rightInverse {R : Type*} [Ring R]
    {M : Type*} [TopologicalSpace M] [AddCommGroup M] {M₂ : Type*} [TopologicalSpace M₂]
    [AddCommGroup M₂] [Module R M] [Module R M₂] [TopologicalAddGroup M] (f₁ : M →L[R] M₂)
    (f₂ : M₂ →L[R] M) (h : Function.RightInverse f₂ f₁) : (ker f₁).ClosedComplemented :=
  ⟨f₁.projKerOfRightInverse f₂ h, f₁.projKerOfRightInverse_apply_idem f₂ h⟩

section Quotient

namespace Submodule

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [TopologicalSpace M]
  (S : Submodule R M)

instance _root_.QuotientModule.Quotient.topologicalSpace : TopologicalSpace (M ⧸ S) :=
  inferInstanceAs (TopologicalSpace (Quotient S.quotientRel))

theorem isOpenMap_mkQ [ContinuousAdd M] : IsOpenMap S.mkQ :=
  QuotientAddGroup.isOpenMap_coe

theorem isOpenQuotientMap_mkQ [ContinuousAdd M] : IsOpenQuotientMap S.mkQ :=
  QuotientAddGroup.isOpenQuotientMap_mk

instance topologicalAddGroup_quotient [TopologicalAddGroup M] : TopologicalAddGroup (M ⧸ S) :=
  inferInstanceAs <| TopologicalAddGroup (M ⧸ S.toAddSubgroup)

instance continuousSMul_quotient [TopologicalSpace R] [TopologicalAddGroup M] [ContinuousSMul R M] :
    ContinuousSMul R (M ⧸ S) where
  continuous_smul := by
    rw [← (IsOpenQuotientMap.id.prodMap S.isOpenQuotientMap_mkQ).continuous_comp_iff]
    exact continuous_quot_mk.comp continuous_smul

instance t3_quotient_of_isClosed [TopologicalAddGroup M] [IsClosed (S : Set M)] :
    T3Space (M ⧸ S) :=
  letI : IsClosed (S.toAddSubgroup : Set M) := ‹_›
  QuotientAddGroup.instT3Space S.toAddSubgroup

end Submodule

end Quotient

namespace MulOpposite

variable (R : Type*) [Semiring R] [τR : TopologicalSpace R] [TopologicalSemiring R]
  {M : Type*} [AddCommMonoid M] [Module R M] [TopologicalSpace M] [ContinuousSMul R M]

@[simps!]
def opContinuousLinearEquiv : M ≃L[R] Mᵐᵒᵖ where
  __ := MulOpposite.opLinearEquiv R

end MulOpposite

set_option linter.style.longFile 2700
