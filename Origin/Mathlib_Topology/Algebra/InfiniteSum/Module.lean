/-
Extracted from Topology/Algebra/InfiniteSum/Module.lean
Genuine: 19 of 19 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Infinite sums in topological vector spaces -/

variable {α β γ δ : Type*}

open Filter Finset Function

section ConstSMul

variable [TopologicalSpace α] [AddCommMonoid α] [DistribSMul γ α]
  [ContinuousConstSMul γ α] {f : β → α} {L : SummationFilter β}

theorem HasSum.const_smul {a : α} (b : γ) (hf : HasSum f a L) :
    HasSum (fun i ↦ b • f i) (b • a) L :=
  hf.map (DistribSMul.toAddMonoidHom α _) <| continuous_const_smul _

theorem Summable.const_smul (b : γ) (hf : Summable f L) : Summable (fun i ↦ b • f i) L :=
  (hf.hasSum.const_smul _).summable

protected theorem Summable.tsum_const_smul [T2Space α] [L.NeBot] (b : γ) (hf : Summable f L) :
    ∑'[L] i, b • f i = b • ∑'[L] i, f i :=
  (hf.hasSum.const_smul _).tsum_eq

lemma tsum_const_smul' {γ : Type*} [Group γ] [DistribMulAction γ α] [ContinuousConstSMul γ α]
    [T2Space α] (g : γ) :
    ∑'[L] (i : β), g • f i = g • ∑'[L] (i : β), f i :=
  ((Homeomorph.smul g).isClosedEmbedding.map_tsum f (g := show α ≃+ α from
    { DistribSMul.toAddMonoidHom _ g with
      invFun := DistribSMul.toAddMonoidHom _ g⁻¹
      left_inv a := by simp, right_inv a := by simp })).symm

lemma tsum_const_smul'' {γ : Type*} [DivisionSemiring γ] [Module γ α] [ContinuousConstSMul γ α]
    [T2Space α] (g : γ) :
    ∑'[L] (i : β), g • f i = g • ∑'[L] (i : β), f i := by
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  · exact tsum_const_smul' (Units.mk0 g hg)

end ConstSMul

variable {ι κ R R₂ M M₂ : Type*}

section SMulConst

variable [Semiring R] [TopologicalSpace R] [TopologicalSpace M] [AddCommMonoid M] [Module R M]
  [ContinuousSMul R M] {f : ι → R} {L : SummationFilter ι}

theorem HasSum.smul_const {r : R} (hf : HasSum f r L) (a : M) :
    HasSum (fun z ↦ f z • a) (r • a) L :=
  hf.map ((smulAddHom R M).flip a) (continuous_id.smul continuous_const)

theorem Summable.smul_const (hf : Summable f L) (a : M) : Summable (fun z ↦ f z • a) L :=
  (hf.hasSum.smul_const _).summable

protected theorem Summable.tsum_smul_const [T2Space M] [L.NeBot] (hf : Summable f L) (a : M) :
    ∑'[L] z, f z • a = (∑'[L] z, f z) • a :=
  (hf.hasSum.smul_const _).tsum_eq

end SMulConst

/-!
Note we cannot derive the `mul` lemmas from these `smul` lemmas, as the `mul` versions do not
require associativity, but `Module` does.
-/

section tsum_smul_tsum

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable [TopologicalSpace R] [TopologicalSpace M] [T3Space M]

variable [ContinuousAdd M] [ContinuousSMul R M]

variable {f : ι → R} {g : κ → M} {s : R} {t u : M}

theorem HasSum.smul_eq (hf : HasSum f s) (hg : HasSum g t)
    (hfg : HasSum (fun x : ι × κ ↦ f x.1 • g x.2) u) : s • t = u :=
  have key₁ : HasSum (fun i ↦ f i • t) (s • t) := hf.smul_const t
  have this : ∀ i : ι, HasSum (fun c : κ ↦ f i • g c) (f i • t) := fun i ↦ hg.const_smul (f i)
  have key₂ : HasSum (fun i ↦ f i • t) u := HasSum.prod_fiberwise hfg this
  key₁.unique key₂

theorem HasSum.smul (hf : HasSum f s) (hg : HasSum g t)
    (hfg : Summable fun x : ι × κ ↦ f x.1 • g x.2) :
    HasSum (fun x : ι × κ ↦ f x.1 • g x.2) (s • t) :=
  let ⟨_u, hu⟩ := hfg
  (hf.smul_eq hg hu).symm ▸ hu

theorem tsum_smul_tsum (hf : Summable f) (hg : Summable g)
    (hfg : Summable fun x : ι × κ ↦ f x.1 • g x.2) :
    ((∑' x, f x) • ∑' y, g y) = ∑' z : ι × κ, f z.1 • g z.2 :=
  hf.hasSum.smul_eq hg.hasSum hfg.hasSum

end tsum_smul_tsum

section HasSum

variable [Semiring R] [Semiring R₂] [AddCommMonoid M] [Module R M] [AddCommMonoid M₂] [Module R₂ M₂]
  [TopologicalSpace M] [TopologicalSpace M₂] {σ : R →+* R₂} {σ' : R₂ →+* R} [RingHomInvPair σ σ']
  [RingHomInvPair σ' σ] {L : SummationFilter ι}

protected theorem ContinuousLinearMap.hasSum {f : ι → M} (φ : M →SL[σ] M₂) {x : M}
    (hf : HasSum f x L) : HasSum (fun b : ι ↦ φ (f b)) (φ x) L := by
  simpa only using hf.map φ.toLinearMap.toAddMonoidHom φ.continuous

alias HasSum.mapL := ContinuousLinearMap.hasSum

protected theorem ContinuousLinearMap.summable {f : ι → M} (φ : M →SL[σ] M₂) (hf : Summable f L) :
    Summable (fun b : ι ↦ φ (f b)) L :=
  (hf.hasSum.mapL φ).summable

alias Summable.mapL := ContinuousLinearMap.summable

protected theorem ContinuousLinearMap.map_tsum [T2Space M₂] [L.NeBot] {f : ι → M} (φ : M →SL[σ] M₂)
    (hf : Summable f L) : φ (∑'[L] z, f z) = ∑'[L] z, φ (f z) :=
  (hf.hasSum.mapL φ).tsum_eq.symm

protected theorem ContinuousLinearEquiv.hasSum {f : ι → M} (e : M ≃SL[σ] M₂) {y : M₂} :
    HasSum (fun b : ι ↦ e (f b)) y L ↔ HasSum f (e.symm y) L :=
  ⟨fun h ↦ by simpa only [e.symm.coe_coe, e.symm_apply_apply] using h.mapL (e.symm : M₂ →SL[σ'] M),
    fun h ↦ by simpa only [e.coe_coe, e.apply_symm_apply] using (e : M →SL[σ] M₂).hasSum h⟩

protected theorem ContinuousLinearEquiv.hasSum' {f : ι → M} (e : M ≃SL[σ] M₂) {x : M} :
    HasSum (fun b : ι ↦ e (f b)) (e x) L ↔ HasSum f x L := by
  rw [e.hasSum, ContinuousLinearEquiv.symm_apply_apply]

protected theorem ContinuousLinearEquiv.summable {f : ι → M} (e : M ≃SL[σ] M₂) :
    (Summable (fun b : ι ↦ e (f b)) L) ↔ Summable f L :=
  ⟨fun hf ↦ (e.hasSum.1 hf.hasSum).summable, (e : M →SL[σ] M₂).summable⟩

theorem ContinuousLinearEquiv.tsum_eq_iff [T2Space M] [T2Space M₂]
    {f : ι → M} (e : M ≃SL[σ] M₂) {y : M₂} :
    (∑'[L] z, e (f z)) = y ↔ ∑'[L] z, f z = e.symm y := by
  by_cases hf : Summable f L
  · by_cases hL : L.NeBot
    · exact ⟨fun h ↦ (e.hasSum.mp ((e.summable.mpr hf).hasSum_iff.mpr h)).tsum_eq, fun h ↦
        (e.hasSum.mpr (hf.hasSum_iff.mpr h)).tsum_eq⟩
    · simp only [tsum_bot hL, eq_symm_apply]
      constructor <;> rintro rfl
      exacts [e.map_finsum f, (e.map_finsum f).symm]
  · have hf' : ¬Summable (fun z ↦ e (f z)) L := fun h ↦ hf (e.summable.mp h)
    rw [tsum_eq_zero_of_not_summable hf, tsum_eq_zero_of_not_summable hf']
    refine ⟨?_, fun H ↦ ?_⟩
    · rintro rfl
      simp
    · simpa using congr_arg (fun z ↦ e z) H

protected theorem ContinuousLinearEquiv.map_tsum [T2Space M] [T2Space M₂]
    {f : ι → M} (e : M ≃SL[σ] M₂) : e (∑'[L] z, f z) = ∑'[L] z, e (f z) := by
  refine symm (e.tsum_eq_iff.mpr ?_)
  rw [e.symm_apply_apply _]

end HasSum

section automorphize

variable {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [T2Space M] {R : Type*}
  [DivisionRing R] [Module R M] [ContinuousConstSMul R M]
