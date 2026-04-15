/-
Extracted from Topology/Algebra/Module/FiniteDimension.lean
Genuine: 27 | Conflates: 0 | Dissolved: 5 | Infrastructure: 15
-/
import Origin.Core
import Mathlib.Analysis.LocallyConvex.BalancedCoreHull
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.Topology.Algebra.Module.Simple
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Finite dimensional topological vector spaces over complete fields

Let `𝕜` be a complete nontrivially normed field, and `E` a topological vector space (TVS) over
`𝕜` (i.e we have `[AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [TopologicalAddGroup E]`
and `[ContinuousSMul 𝕜 E]`).

If `E` is finite dimensional and Hausdorff, then all linear maps from `E` to any other TVS are
continuous.

When `E` is a normed space, this gets us the equivalence of norms in finite dimension.

## Main results :

* `LinearMap.continuous_iff_isClosed_ker` : a linear form is continuous if and only if its kernel
  is closed.
* `LinearMap.continuous_of_finiteDimensional` : a linear map on a finite-dimensional Hausdorff
  space over a complete field is continuous.

## TODO

Generalize more of `Mathlib.Analysis.Normed.Module.FiniteDimension` to general TVSs.

## Implementation detail

The main result from which everything follows is the fact that, if `ξ : ι → E` is a finite basis,
then `ξ.equivFun : E →ₗ (ι → 𝕜)` is continuous. However, for technical reasons, it is easier to
prove this when `ι` and `E` live in the same universe. So we start by doing that as a private
lemma, then we deduce `LinearMap.continuous_of_finiteDimensional` from it, and then the general
result follows as `continuous_equivFun_basis`.

-/

open Filter Module Set TopologicalSpace Topology

universe u v w x

noncomputable section

section Field

variable {𝕜 E F : Type*} [Field 𝕜] [TopologicalSpace 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [TopologicalAddGroup F]
  [ContinuousSMul 𝕜 F]

instance [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] : FiniteDimensional 𝕜 (E →L[𝕜] F) :=
  FiniteDimensional.of_injective (ContinuousLinearMap.coeLM 𝕜 : (E →L[𝕜] F) →ₗ[𝕜] E →ₗ[𝕜] F)
    ContinuousLinearMap.coe_injective

end Field

section NormedField

variable {𝕜 : Type u} [hnorm : NontriviallyNormedField 𝕜] {E : Type v} [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] [TopologicalAddGroup E] [ContinuousSMul 𝕜 E] {F : Type w} [AddCommGroup F]
  [Module 𝕜 F] [TopologicalSpace F] [TopologicalAddGroup F] [ContinuousSMul 𝕜 F] {F' : Type x}
  [AddCommGroup F'] [Module 𝕜 F'] [TopologicalSpace F'] [TopologicalAddGroup F']
  [ContinuousSMul 𝕜 F']

theorem unique_topology_of_t2 {t : TopologicalSpace 𝕜} (h₁ : @TopologicalAddGroup 𝕜 t _)
    (h₂ : @ContinuousSMul 𝕜 𝕜 _ hnorm.toUniformSpace.toTopologicalSpace t) (h₃ : @T2Space 𝕜 t) :
    t = hnorm.toUniformSpace.toTopologicalSpace := by
  -- Let `𝓣₀` denote the topology on `𝕜` induced by the norm, and `𝓣` be any T2 vector
  -- topology on `𝕜`. To show that `𝓣₀ = 𝓣`, it suffices to show that they have the same
  -- neighborhoods of 0.
  refine TopologicalAddGroup.ext h₁ inferInstance (le_antisymm ?_ ?_)
  · -- To show `𝓣 ≤ 𝓣₀`, we have to show that closed balls are `𝓣`-neighborhoods of 0.
    rw [Metric.nhds_basis_closedBall.ge_iff]
    -- Let `ε > 0`. Since `𝕜` is nontrivially normed, we have `0 < ‖ξ₀‖ < ε` for some `ξ₀ : 𝕜`.
    intro ε hε
    rcases NormedField.exists_norm_lt 𝕜 hε with ⟨ξ₀, hξ₀, hξ₀ε⟩
    -- Since `ξ₀ ≠ 0` and `𝓣` is T2, we know that `{ξ₀}ᶜ` is a `𝓣`-neighborhood of 0.
    -- Porting note: added `mem_compl_singleton_iff.mpr`
    have : {ξ₀}ᶜ ∈ @nhds 𝕜 t 0 := IsOpen.mem_nhds isOpen_compl_singleton <|
      mem_compl_singleton_iff.mpr <| Ne.symm <| norm_ne_zero_iff.mp hξ₀.ne.symm
    -- Thus, its balanced core `𝓑` is too. Let's show that the closed ball of radius `ε` contains
    -- `𝓑`, which will imply that the closed ball is indeed a `𝓣`-neighborhood of 0.
    have : balancedCore 𝕜 {ξ₀}ᶜ ∈ @nhds 𝕜 t 0 := balancedCore_mem_nhds_zero this
    refine mem_of_superset this fun ξ hξ => ?_
    -- Let `ξ ∈ 𝓑`. We want to show `‖ξ‖ < ε`. If `ξ = 0`, this is trivial.
    by_cases hξ0 : ξ = 0
    · rw [hξ0]
      exact Metric.mem_closedBall_self hε.le
    · rw [mem_closedBall_zero_iff]
      -- Now suppose `ξ ≠ 0`. By contradiction, let's assume `ε < ‖ξ‖`, and show that
      -- `ξ₀ ∈ 𝓑 ⊆ {ξ₀}ᶜ`, which is a contradiction.
      by_contra! h
      suffices (ξ₀ * ξ⁻¹) • ξ ∈ balancedCore 𝕜 {ξ₀}ᶜ by
        rw [smul_eq_mul 𝕜, mul_assoc, inv_mul_cancel₀ hξ0, mul_one] at this
        exact not_mem_compl_iff.mpr (mem_singleton ξ₀) ((balancedCore_subset _) this)
      -- For that, we use that `𝓑` is balanced : since `‖ξ₀‖ < ε < ‖ξ‖`, we have `‖ξ₀ / ξ‖ ≤ 1`,
      -- hence `ξ₀ = (ξ₀ / ξ) • ξ ∈ 𝓑` because `ξ ∈ 𝓑`.
      refine (balancedCore_balanced _).smul_mem ?_ hξ
      rw [norm_mul, norm_inv, mul_inv_le_iff₀ (norm_pos_iff.mpr hξ0), one_mul]
      exact (hξ₀ε.trans h).le
  · -- Finally, to show `𝓣₀ ≤ 𝓣`, we simply argue that `id = (fun x ↦ x • 1)` is continuous from
    -- `(𝕜, 𝓣₀)` to `(𝕜, 𝓣)` because `(•) : (𝕜, 𝓣₀) × (𝕜, 𝓣) → (𝕜, 𝓣)` is continuous.
    calc
      @nhds 𝕜 hnorm.toUniformSpace.toTopologicalSpace 0 =
          map id (@nhds 𝕜 hnorm.toUniformSpace.toTopologicalSpace 0) :=
        map_id.symm
      _ = map (fun x => id x • (1 : 𝕜)) (@nhds 𝕜 hnorm.toUniformSpace.toTopologicalSpace 0) := by
        conv_rhs =>
          congr
          ext
          rw [smul_eq_mul, mul_one]
      _ ≤ @nhds 𝕜 t ((0 : 𝕜) • (1 : 𝕜)) :=
        (@Tendsto.smul_const _ _ _ hnorm.toUniformSpace.toTopologicalSpace t _ _ _ _ _
          tendsto_id (1 : 𝕜))
      _ = @nhds 𝕜 t 0 := by rw [zero_smul]

theorem LinearMap.continuous_of_isClosed_ker (l : E →ₗ[𝕜] 𝕜)
    (hl : IsClosed (LinearMap.ker l : Set E)) :
    Continuous l := by
  -- `l` is either constant or surjective. If it is constant, the result is trivial.
  by_cases H : finrank 𝕜 (LinearMap.range l) = 0
  · rw [Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at H
    rw [H]
    exact continuous_zero
  · -- In the case where `l` is surjective, we factor it as `φ : (E ⧸ l.ker) ≃ₗ[𝕜] 𝕜`. Note that
    -- `E ⧸ l.ker` is T2 since `l.ker` is closed.
    have : finrank 𝕜 (LinearMap.range l) = 1 :=
      le_antisymm (finrank_self 𝕜 ▸ l.range.finrank_le) (zero_lt_iff.mpr H)
    have hi : Function.Injective ((LinearMap.ker l).liftQ l (le_refl _)) := by
      rw [← LinearMap.ker_eq_bot]
      exact Submodule.ker_liftQ_eq_bot _ _ _ (le_refl _)
    have hs : Function.Surjective ((LinearMap.ker l).liftQ l (le_refl _)) := by
      rw [← LinearMap.range_eq_top, Submodule.range_liftQ]
      exact Submodule.eq_top_of_finrank_eq ((finrank_self 𝕜).symm ▸ this)
    let φ : (E ⧸ LinearMap.ker l) ≃ₗ[𝕜] 𝕜 :=
      LinearEquiv.ofBijective ((LinearMap.ker l).liftQ l (le_refl _)) ⟨hi, hs⟩
    have hlφ : (l : E → 𝕜) = φ ∘ (LinearMap.ker l).mkQ := by ext; rfl
    -- Since the quotient map `E →ₗ[𝕜] (E ⧸ l.ker)` is continuous, the continuity of `l` will follow
    -- form the continuity of `φ`.
    suffices Continuous φ.toEquiv by
      rw [hlφ]
      exact this.comp continuous_quot_mk
    -- The pullback by `φ.symm` of the quotient topology is a T2 topology on `𝕜`, because `φ.symm`
    -- is injective. Since `φ.symm` is linear, it is also a vector space topology.
    -- Hence, we know that it is equal to the topology induced by the norm.
    have : induced φ.toEquiv.symm inferInstance = hnorm.toUniformSpace.toTopologicalSpace := by
      refine unique_topology_of_t2 (topologicalAddGroup_induced φ.symm.toLinearMap)
        (continuousSMul_induced φ.symm.toMulActionHom) ?_
      -- Porting note: was `rw [t2Space_iff]`
      refine (@t2Space_iff 𝕜 (induced (↑(LinearEquiv.toEquiv φ).symm) inferInstance)).mpr ?_
      exact fun x y hxy =>
        @separated_by_continuous _ _ (induced _ _) _ _ _ continuous_induced_dom _ _
          (φ.toEquiv.symm.injective.ne hxy)
    -- Finally, the pullback by `φ.symm` is exactly the pushforward by `φ`, so we have to prove
    -- that `φ` is continuous when `𝕜` is endowed with the pushforward by `φ` of the quotient
    -- topology, which is trivial by definition of the pushforward.
    rw [this.symm, Equiv.induced_symm]
    exact continuous_coinduced_rng

theorem LinearMap.continuous_iff_isClosed_ker (l : E →ₗ[𝕜] 𝕜) :
    Continuous l ↔ IsClosed (LinearMap.ker l : Set E) :=
  ⟨fun h => isClosed_singleton.preimage h, l.continuous_of_isClosed_ker⟩

-- DISSOLVED: LinearMap.continuous_of_nonzero_on_open

variable [CompleteSpace 𝕜]

private theorem continuous_equivFun_basis_aux [T2Space E] {ι : Type v} [Fintype ι]
    (ξ : Basis ι 𝕜 E) : Continuous ξ.equivFun := by
  letI : UniformSpace E := TopologicalAddGroup.toUniformSpace E
  letI : UniformAddGroup E := comm_topologicalAddGroup_is_uniform
  induction' hn : Fintype.card ι with n IH generalizing ι E
  · rw [Fintype.card_eq_zero_iff] at hn
    exact continuous_of_const fun x y => funext hn.elim
  · haveI : FiniteDimensional 𝕜 E := .of_fintype_basis ξ
    -- first step: thanks to the induction hypothesis, any n-dimensional subspace is equivalent
    -- to a standard space of dimension n, hence it is complete and therefore closed.
    have H₁ : ∀ s : Submodule 𝕜 E, finrank 𝕜 s = n → IsClosed (s : Set E) := by
      intro s s_dim
      letI : UniformAddGroup s := s.toAddSubgroup.uniformAddGroup
      let b := Basis.ofVectorSpace 𝕜 s
      have U : IsUniformEmbedding b.equivFun.symm.toEquiv := by
        have : Fintype.card (Basis.ofVectorSpaceIndex 𝕜 s) = n := by
          rw [← s_dim]
          exact (finrank_eq_card_basis b).symm
        have : Continuous b.equivFun := IH b this
        exact
          b.equivFun.symm.isUniformEmbedding b.equivFun.symm.toLinearMap.continuous_on_pi this
      have : IsComplete (s : Set E) :=
        completeSpace_coe_iff_isComplete.1 ((completeSpace_congr U).1 inferInstance)
      exact this.isClosed
    -- second step: any linear form is continuous, as its kernel is closed by the first step
    have H₂ : ∀ f : E →ₗ[𝕜] 𝕜, Continuous f := by
      intro f
      by_cases H : finrank 𝕜 (LinearMap.range f) = 0
      · rw [Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at H
        rw [H]
        exact continuous_zero
      · have : finrank 𝕜 (LinearMap.ker f) = n := by
          have Z := f.finrank_range_add_finrank_ker
          rw [finrank_eq_card_basis ξ, hn] at Z
          have : finrank 𝕜 (LinearMap.range f) = 1 :=
            le_antisymm (finrank_self 𝕜 ▸ f.range.finrank_le) (zero_lt_iff.mpr H)
          rw [this, add_comm, Nat.add_one] at Z
          exact Nat.succ.inj Z
        have : IsClosed (LinearMap.ker f : Set E) := H₁ _ this
        exact LinearMap.continuous_of_isClosed_ker f this
    rw [continuous_pi_iff]
    intro i
    change Continuous (ξ.coord i)
    exact H₂ (ξ.coord i)

theorem LinearMap.continuous_of_finiteDimensional [T2Space E] [FiniteDimensional 𝕜 E]
    (f : E →ₗ[𝕜] F') : Continuous f := by
  -- for the proof, go to a model vector space `b → 𝕜` thanks to `continuous_equivFun_basis`, and
  -- argue that all linear maps there are continuous.
  let b := Basis.ofVectorSpace 𝕜 E
  have A : Continuous b.equivFun := continuous_equivFun_basis_aux b
  have B : Continuous (f.comp (b.equivFun.symm : (Basis.ofVectorSpaceIndex 𝕜 E → 𝕜) →ₗ[𝕜] E)) :=
    LinearMap.continuous_on_pi _
  have :
    Continuous
      (f.comp (b.equivFun.symm : (Basis.ofVectorSpaceIndex 𝕜 E → 𝕜) →ₗ[𝕜] E) ∘ b.equivFun) :=
    B.comp A
  convert this
  ext x
  dsimp
  rw [Basis.equivFun_symm_apply, Basis.sum_repr]

instance LinearMap.continuousLinearMapClassOfFiniteDimensional [T2Space E] [FiniteDimensional 𝕜 E] :
    ContinuousLinearMapClass (E →ₗ[𝕜] F') 𝕜 E F' :=
  { LinearMap.semilinearMapClass with map_continuous := fun f => f.continuous_of_finiteDimensional }

theorem continuous_equivFun_basis [T2Space E] {ι : Type*} [Finite ι] (ξ : Basis ι 𝕜 E) :
    Continuous ξ.equivFun :=
  haveI : FiniteDimensional 𝕜 E := .of_fintype_basis ξ
  ξ.equivFun.toLinearMap.continuous_of_finiteDimensional

namespace LinearMap

variable [T2Space E] [FiniteDimensional 𝕜 E]

def toContinuousLinearMap : (E →ₗ[𝕜] F') ≃ₗ[𝕜] E →L[𝕜] F' where
  toFun f := ⟨f, f.continuous_of_finiteDimensional⟩
  invFun := (↑)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := ContinuousLinearMap.coe_injective rfl

def _root_.Module.End.toContinuousLinearMap (E : Type v) [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] : (E →ₗ[𝕜] E) ≃ₐ[𝕜] (E →L[𝕜] E) :=
  { LinearMap.toContinuousLinearMap with
    map_mul' := fun _ _ ↦ rfl
    commutes' := fun _ ↦ rfl }

@[simp]
theorem coe_toContinuousLinearMap' (f : E →ₗ[𝕜] F') : ⇑(LinearMap.toContinuousLinearMap f) = f :=
  rfl

@[simp]
theorem coe_toContinuousLinearMap (f : E →ₗ[𝕜] F') :
    ((LinearMap.toContinuousLinearMap f) : E →ₗ[𝕜] F') = f :=
  rfl

@[simp]
theorem coe_toContinuousLinearMap_symm :
    ⇑(toContinuousLinearMap : (E →ₗ[𝕜] F') ≃ₗ[𝕜] E →L[𝕜] F').symm =
      ((↑) : (E →L[𝕜] F') → E →ₗ[𝕜] F') :=
  rfl

@[simp]
theorem det_toContinuousLinearMap (f : E →ₗ[𝕜] E) :
    (LinearMap.toContinuousLinearMap f).det = LinearMap.det f :=
  rfl

@[simp]
theorem ker_toContinuousLinearMap (f : E →ₗ[𝕜] F') :
    ker (LinearMap.toContinuousLinearMap f) = ker f :=
  rfl

@[simp]
theorem range_toContinuousLinearMap (f : E →ₗ[𝕜] F') :
    range (LinearMap.toContinuousLinearMap f) = range f :=
  rfl

theorem isOpenMap_of_finiteDimensional (f : F →ₗ[𝕜] E) (hf : Function.Surjective f) :
    IsOpenMap f := by
  obtain ⟨g, hg⟩ := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hf)
  refine IsOpenMap.of_sections fun x => ⟨fun y => g (y - f x) + x, ?_, ?_, fun y => ?_⟩
  · exact
      ((g.continuous_of_finiteDimensional.comp <| continuous_id.sub continuous_const).add
          continuous_const).continuousAt
  · simp only
    rw [sub_self, map_zero, zero_add]
  · simp only [map_sub, map_add, ← comp_apply f g, hg, id_apply, sub_add_cancel]

instance canLiftContinuousLinearMap : CanLift (E →ₗ[𝕜] F) (E →L[𝕜] F) (↑) fun _ => True :=
  ⟨fun f _ => ⟨LinearMap.toContinuousLinearMap f, rfl⟩⟩

end LinearMap

section

variable [T2Space E] [T2Space F] [FiniteDimensional 𝕜 E]

namespace LinearEquiv

def toContinuousLinearEquiv (e : E ≃ₗ[𝕜] F) : E ≃L[𝕜] F :=
  { e with
    continuous_toFun := e.toLinearMap.continuous_of_finiteDimensional
    continuous_invFun :=
      haveI : FiniteDimensional 𝕜 F := e.finiteDimensional
      e.symm.toLinearMap.continuous_of_finiteDimensional }

@[simp]
theorem coe_toContinuousLinearEquiv (e : E ≃ₗ[𝕜] F) : (e.toContinuousLinearEquiv : E →ₗ[𝕜] F) = e :=
  rfl

@[simp]
theorem coe_toContinuousLinearEquiv' (e : E ≃ₗ[𝕜] F) : (e.toContinuousLinearEquiv : E → F) = e :=
  rfl

@[simp]
theorem coe_toContinuousLinearEquiv_symm (e : E ≃ₗ[𝕜] F) :
    (e.toContinuousLinearEquiv.symm : F →ₗ[𝕜] E) = e.symm :=
  rfl

@[simp]
theorem coe_toContinuousLinearEquiv_symm' (e : E ≃ₗ[𝕜] F) :
    (e.toContinuousLinearEquiv.symm : F → E) = e.symm :=
  rfl

@[simp]
theorem toLinearEquiv_toContinuousLinearEquiv (e : E ≃ₗ[𝕜] F) :
    e.toContinuousLinearEquiv.toLinearEquiv = e := by
  ext x
  rfl

theorem toLinearEquiv_toContinuousLinearEquiv_symm (e : E ≃ₗ[𝕜] F) :
    e.toContinuousLinearEquiv.symm.toLinearEquiv = e.symm := by
  ext x
  rfl

instance canLiftContinuousLinearEquiv :
    CanLift (E ≃ₗ[𝕜] F) (E ≃L[𝕜] F) ContinuousLinearEquiv.toLinearEquiv fun _ => True :=
  ⟨fun f _ => ⟨_, f.toLinearEquiv_toContinuousLinearEquiv⟩⟩

end LinearEquiv

variable [FiniteDimensional 𝕜 F]

theorem FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq
    (cond : finrank 𝕜 E = finrank 𝕜 F) : Nonempty (E ≃L[𝕜] F) :=
  (nonempty_linearEquiv_of_finrank_eq cond).map LinearEquiv.toContinuousLinearEquiv

theorem FiniteDimensional.nonempty_continuousLinearEquiv_iff_finrank_eq :
    Nonempty (E ≃L[𝕜] F) ↔ finrank 𝕜 E = finrank 𝕜 F :=
  ⟨fun ⟨h⟩ => h.toLinearEquiv.finrank_eq, fun h =>
    FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq h⟩

def ContinuousLinearEquiv.ofFinrankEq (cond : finrank 𝕜 E = finrank 𝕜 F) : E ≃L[𝕜] F :=
  (LinearEquiv.ofFinrankEq E F cond).toContinuousLinearEquiv

end

namespace Basis

variable {ι : Type*} [Finite ι] [T2Space E]

def constrL (v : Basis ι 𝕜 E) (f : ι → F) : E →L[𝕜] F :=
  haveI : FiniteDimensional 𝕜 E := FiniteDimensional.of_fintype_basis v
  LinearMap.toContinuousLinearMap (v.constr 𝕜 f)

@[simp] -- Porting note: removed `norm_cast`
theorem coe_constrL (v : Basis ι 𝕜 E) (f : ι → F) : (v.constrL f : E →ₗ[𝕜] F) = v.constr 𝕜 f :=
  rfl

@[simps! apply]
def equivFunL (v : Basis ι 𝕜 E) : E ≃L[𝕜] ι → 𝕜 :=
  { v.equivFun with
    continuous_toFun :=
      haveI : FiniteDimensional 𝕜 E := FiniteDimensional.of_fintype_basis v
      v.equivFun.toLinearMap.continuous_of_finiteDimensional
    continuous_invFun := by
      change Continuous v.equivFun.symm.toFun
      exact v.equivFun.symm.toLinearMap.continuous_of_finiteDimensional }

@[simp]
lemma equivFunL_symm_apply_repr (v : Basis ι 𝕜 E) (x : E) :
    v.equivFunL.symm (v.repr x) = x :=
  v.equivFunL.symm_apply_apply x

@[simp]
theorem constrL_apply {ι : Type*} [Fintype ι] (v : Basis ι 𝕜 E) (f : ι → F) (e : E) :
    v.constrL f e = ∑ i, v.equivFun e i • f i :=
  v.constr_apply_fintype 𝕜 _ _

@[simp 1100]
theorem constrL_basis (v : Basis ι 𝕜 E) (f : ι → F) (i : ι) : v.constrL f (v i) = f i :=
  v.constr_basis 𝕜 _ _

end Basis

namespace ContinuousLinearMap

variable [T2Space E] [FiniteDimensional 𝕜 E]

-- DISSOLVED: toContinuousLinearEquivOfDetNeZero

-- DISSOLVED: coe_toContinuousLinearEquivOfDetNeZero

-- DISSOLVED: toContinuousLinearEquivOfDetNeZero_apply

theorem _root_.Matrix.toLin_finTwoProd_toContinuousLinearMap (a b c d : 𝕜) :
    LinearMap.toContinuousLinearMap
      (Matrix.toLin (Basis.finTwoProd 𝕜) (Basis.finTwoProd 𝕜) !![a, b; c, d]) =
      (a • ContinuousLinearMap.fst 𝕜 𝕜 𝕜 + b • ContinuousLinearMap.snd 𝕜 𝕜 𝕜).prod
        (c • ContinuousLinearMap.fst 𝕜 𝕜 𝕜 + d • ContinuousLinearMap.snd 𝕜 𝕜 𝕜) :=
  ContinuousLinearMap.ext <| Matrix.toLin_finTwoProd_apply _ _ _ _

end ContinuousLinearMap

end NormedField

section UniformAddGroup

variable (𝕜 E : Type*) [NontriviallyNormedField 𝕜]
  [CompleteSpace 𝕜] [AddCommGroup E] [UniformSpace E] [T2Space E] [UniformAddGroup E]
  [Module 𝕜 E] [ContinuousSMul 𝕜 E]

include 𝕜 in

theorem FiniteDimensional.complete [FiniteDimensional 𝕜 E] : CompleteSpace E := by
  set e := ContinuousLinearEquiv.ofFinrankEq (@finrank_fin_fun 𝕜 _ _ (finrank 𝕜 E)).symm
  have : IsUniformEmbedding e.toEquiv.symm := e.symm.isUniformEmbedding
  exact (completeSpace_congr this).1 inferInstance

variable {𝕜 E}

theorem Submodule.complete_of_finiteDimensional (s : Submodule 𝕜 E) [FiniteDimensional 𝕜 s] :
    IsComplete (s : Set E) :=
  haveI : UniformAddGroup s := s.toAddSubgroup.uniformAddGroup
  completeSpace_coe_iff_isComplete.1 (FiniteDimensional.complete 𝕜 s)

end UniformAddGroup

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
   [AddCommGroup E] [TopologicalSpace E] [TopologicalAddGroup E] [Module 𝕜 E]
   [ContinuousSMul 𝕜 E]
   [AddCommGroup F] [TopologicalSpace F] [T2Space F] [TopologicalAddGroup F] [Module 𝕜 F]
   [ContinuousSMul 𝕜 F]

theorem Submodule.closed_of_finiteDimensional
    [T2Space E] (s : Submodule 𝕜 E) [FiniteDimensional 𝕜 s] :
    IsClosed (s : Set E) :=
  letI := TopologicalAddGroup.toUniformSpace E
  haveI : UniformAddGroup E := comm_topologicalAddGroup_is_uniform
  s.complete_of_finiteDimensional.isClosed

theorem LinearMap.isClosedEmbedding_of_injective [T2Space E] [FiniteDimensional 𝕜 E] {f : E →ₗ[𝕜] F}
    (hf : LinearMap.ker f = ⊥) : IsClosedEmbedding f :=
  let g := LinearEquiv.ofInjective f (LinearMap.ker_eq_bot.mp hf)
  { IsEmbedding.subtypeVal.comp g.toContinuousLinearEquiv.toHomeomorph.isEmbedding with
    isClosed_range := by
      haveI := f.finiteDimensional_range
      simpa [LinearMap.range_coe f] using f.range.closed_of_finiteDimensional }

alias LinearMap.closedEmbedding_of_injective := LinearMap.isClosedEmbedding_of_injective

-- DISSOLVED: isClosedEmbedding_smul_left

alias closedEmbedding_smul_left := isClosedEmbedding_smul_left

theorem isClosedMap_smul_left [T2Space E] (c : E) : IsClosedMap fun x : 𝕜 => x • c := by
  by_cases hc : c = 0
  · simp_rw [hc, smul_zero]
    exact isClosedMap_const
  · exact (isClosedEmbedding_smul_left hc).isClosedMap

theorem ContinuousLinearMap.exists_right_inverse_of_surjective [FiniteDimensional 𝕜 F]
    (f : E →L[𝕜] F) (hf : LinearMap.range f = ⊤) :
    ∃ g : F →L[𝕜] E, f.comp g = ContinuousLinearMap.id 𝕜 F :=
  let ⟨g, hg⟩ := (f : E →ₗ[𝕜] F).exists_rightInverse_of_surjective hf
  ⟨LinearMap.toContinuousLinearMap g, ContinuousLinearMap.coe_inj.1 hg⟩
