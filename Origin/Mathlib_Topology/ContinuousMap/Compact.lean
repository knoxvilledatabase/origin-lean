/-
Extracted from Topology/ContinuousMap/Compact.lean
Genuine: 35 of 68 | Dissolved: 0 | Infrastructure: 33
-/
import Origin.Core
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.ContinuousMap.Star
import Mathlib.Topology.UniformSpace.Compact
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Sets.Compacts
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Continuous functions on a compact space

Continuous functions `C(α, β)` from a compact space `α` to a metric space `β`
are automatically bounded, and so acquire various structures inherited from `α →ᵇ β`.

This file transfers these structures, and restates some lemmas
characterising these structures.

If you need a lemma which is proved about `α →ᵇ β` but not for `C(α, β)` when `α` is compact,
you should restate it here. You can also use
`ContinuousMap.equivBoundedOfCompact` to move functions back and forth.
-/

noncomputable section

open NNReal BoundedContinuousFunction Set Metric

namespace ContinuousMap

variable {α β E : Type*}

variable [TopologicalSpace α] [CompactSpace α] [PseudoMetricSpace β] [SeminormedAddCommGroup E]

section

variable (α β)

@[simps (config := .asFn)]
def equivBoundedOfCompact : C(α, β) ≃ (α →ᵇ β) :=
  ⟨mkOfCompact, BoundedContinuousFunction.toContinuousMap, fun f => by
    ext
    rfl, fun f => by
    ext
    rfl⟩

theorem isUniformInducing_equivBoundedOfCompact : IsUniformInducing (equivBoundedOfCompact α β) :=
  IsUniformInducing.mk'
    (by
      simp only [hasBasis_compactConvergenceUniformity.mem_iff, uniformity_basis_dist_le.mem_iff]
      exact fun s =>
        ⟨fun ⟨⟨a, b⟩, ⟨_, ⟨ε, hε, hb⟩⟩, hs⟩ =>
          ⟨{ p | ∀ x, (p.1 x, p.2 x) ∈ b }, ⟨ε, hε, fun _ h x => hb ((dist_le hε.le).mp h x)⟩,
            fun f g h => hs fun x _ => h x⟩,
          fun ⟨_, ⟨ε, hε, ht⟩, hs⟩ =>
          ⟨⟨Set.univ, { p | dist p.1 p.2 ≤ ε }⟩, ⟨isCompact_univ, ⟨ε, hε, fun _ h => h⟩⟩,
            fun ⟨f, g⟩ h => hs _ _ (ht ((dist_le hε.le).mpr fun x => h x (mem_univ x)))⟩⟩)

alias uniformInducing_equivBoundedOfCompact := isUniformInducing_equivBoundedOfCompact

theorem isUniformEmbedding_equivBoundedOfCompact : IsUniformEmbedding (equivBoundedOfCompact α β) :=
  { isUniformInducing_equivBoundedOfCompact α β with
    injective := (equivBoundedOfCompact α β).injective }

alias uniformEmbedding_equivBoundedOfCompact := isUniformEmbedding_equivBoundedOfCompact

def addEquivBoundedOfCompact [AddMonoid β] [LipschitzAdd β] : C(α, β) ≃+ (α →ᵇ β) :=
  ({ toContinuousMapAddHom α β, (equivBoundedOfCompact α β).symm with } : (α →ᵇ β) ≃+ C(α, β)).symm

@[simp]
theorem addEquivBoundedOfCompact_symm_apply [AddMonoid β] [LipschitzAdd β] :
    ⇑((addEquivBoundedOfCompact α β).symm) = toContinuousMapAddHom α β :=
  rfl

@[simp]
theorem addEquivBoundedOfCompact_apply [AddMonoid β] [LipschitzAdd β] :
    ⇑(addEquivBoundedOfCompact α β) = mkOfCompact :=
  rfl

instance instPseudoMetricSpace : PseudoMetricSpace C(α, β) :=
  (isUniformEmbedding_equivBoundedOfCompact α β).comapPseudoMetricSpace _

instance instMetricSpace {β : Type*} [MetricSpace β] :
    MetricSpace C(α, β) :=
  (isUniformEmbedding_equivBoundedOfCompact α β).comapMetricSpace _

@[simps! (config := .asFn) toEquiv apply symm_apply]
def isometryEquivBoundedOfCompact : C(α, β) ≃ᵢ (α →ᵇ β) where
  isometry_toFun _ _ := rfl
  toEquiv := equivBoundedOfCompact α β

end

@[simp]
theorem _root_.BoundedContinuousFunction.dist_mkOfCompact (f g : C(α, β)) :
    dist (mkOfCompact f) (mkOfCompact g) = dist f g :=
  rfl

@[simp]
theorem _root_.BoundedContinuousFunction.dist_toContinuousMap (f g : α →ᵇ β) :
    dist f.toContinuousMap g.toContinuousMap = dist f g :=
  rfl

open BoundedContinuousFunction

section

variable {f g : C(α, β)} {C : ℝ}

theorem dist_apply_le_dist (x : α) : dist (f x) (g x) ≤ dist f g := by
  simp only [← dist_mkOfCompact, dist_coe_le_dist, ← mkOfCompact_apply]

theorem dist_le (C0 : (0 : ℝ) ≤ C) : dist f g ≤ C ↔ ∀ x : α, dist (f x) (g x) ≤ C := by
  simp only [← dist_mkOfCompact, BoundedContinuousFunction.dist_le C0, mkOfCompact_apply]

theorem dist_le_iff_of_nonempty [Nonempty α] : dist f g ≤ C ↔ ∀ x, dist (f x) (g x) ≤ C := by
  simp only [← dist_mkOfCompact, BoundedContinuousFunction.dist_le_iff_of_nonempty,
    mkOfCompact_apply]

theorem dist_lt_iff_of_nonempty [Nonempty α] : dist f g < C ↔ ∀ x : α, dist (f x) (g x) < C := by
  simp only [← dist_mkOfCompact, dist_lt_iff_of_nonempty_compact, mkOfCompact_apply]

theorem dist_lt_of_nonempty [Nonempty α] (w : ∀ x : α, dist (f x) (g x) < C) : dist f g < C :=
  dist_lt_iff_of_nonempty.2 w

theorem dist_lt_iff (C0 : (0 : ℝ) < C) : dist f g < C ↔ ∀ x : α, dist (f x) (g x) < C := by
  rw [← dist_mkOfCompact, dist_lt_iff_of_compact C0]
  simp only [mkOfCompact_apply]

instance {R} [Zero R] [Zero β] [PseudoMetricSpace R] [SMul R β] [BoundedSMul R β] :
    BoundedSMul R C(α, β) where
  dist_smul_pair' r f g := by
    simpa only [← dist_mkOfCompact] using dist_smul_pair r (mkOfCompact f) (mkOfCompact g)
  dist_pair_smul' r₁ r₂ f := by
    simpa only [← dist_mkOfCompact] using dist_pair_smul r₁ r₂ (mkOfCompact f)

end

instance : Norm C(α, E) where norm x := dist x 0

@[simp]
theorem _root_.BoundedContinuousFunction.norm_mkOfCompact (f : C(α, E)) : ‖mkOfCompact f‖ = ‖f‖ :=
  rfl

@[simp]
theorem _root_.BoundedContinuousFunction.norm_toContinuousMap_eq (f : α →ᵇ E) :
    ‖f.toContinuousMap‖ = ‖f‖ :=
  rfl

open BoundedContinuousFunction

instance : SeminormedAddCommGroup C(α, E) where
  __ := ContinuousMap.instPseudoMetricSpace _ _
  __ := ContinuousMap.instAddCommGroupContinuousMap
  dist_eq x y := by
    rw [← norm_mkOfCompact, ← dist_mkOfCompact, dist_eq_norm, mkOfCompact_sub]
  dist := dist
  norm := norm

instance {E : Type*} [NormedAddCommGroup E] : NormedAddCommGroup C(α, E) where
  __ : SeminormedAddCommGroup C(α, E) := inferInstance
  __ : MetricSpace C(α, E) := inferInstance

instance [Nonempty α] [One E] [NormOneClass E] : NormOneClass C(α, E) where
  norm_one := by simp only [← norm_mkOfCompact, mkOfCompact_one, norm_one]

section

variable (f : C(α, E))

theorem norm_coe_le_norm (x : α) : ‖f x‖ ≤ ‖f‖ :=
  (mkOfCompact f).norm_coe_le_norm x

theorem dist_le_two_norm (x y : α) : dist (f x) (f y) ≤ 2 * ‖f‖ :=
  (mkOfCompact f).dist_le_two_norm x y

theorem norm_le {C : ℝ} (C0 : (0 : ℝ) ≤ C) : ‖f‖ ≤ C ↔ ∀ x : α, ‖f x‖ ≤ C :=
  @BoundedContinuousFunction.norm_le _ _ _ _ (mkOfCompact f) _ C0

theorem norm_le_of_nonempty [Nonempty α] {M : ℝ} : ‖f‖ ≤ M ↔ ∀ x, ‖f x‖ ≤ M :=
  @BoundedContinuousFunction.norm_le_of_nonempty _ _ _ _ _ (mkOfCompact f) _

theorem norm_lt_iff {M : ℝ} (M0 : 0 < M) : ‖f‖ < M ↔ ∀ x, ‖f x‖ < M :=
  @BoundedContinuousFunction.norm_lt_iff_of_compact _ _ _ _ _ (mkOfCompact f) _ M0

theorem nnnorm_lt_iff {M : ℝ≥0} (M0 : 0 < M) : ‖f‖₊ < M ↔ ∀ x : α, ‖f x‖₊ < M :=
  f.norm_lt_iff M0

theorem norm_lt_iff_of_nonempty [Nonempty α] {M : ℝ} : ‖f‖ < M ↔ ∀ x, ‖f x‖ < M :=
  @BoundedContinuousFunction.norm_lt_iff_of_nonempty_compact _ _ _ _ _ _ (mkOfCompact f) _

theorem nnnorm_lt_iff_of_nonempty [Nonempty α] {M : ℝ≥0} : ‖f‖₊ < M ↔ ∀ x, ‖f x‖₊ < M :=
  f.norm_lt_iff_of_nonempty

theorem apply_le_norm (f : C(α, ℝ)) (x : α) : f x ≤ ‖f‖ :=
  le_trans (le_abs.mpr (Or.inl (le_refl (f x)))) (f.norm_coe_le_norm x)

theorem neg_norm_le_apply (f : C(α, ℝ)) (x : α) : -‖f‖ ≤ f x :=
  le_trans (neg_le_neg (f.norm_coe_le_norm x)) (neg_le.mp (neg_le_abs (f x)))

theorem nnnorm_eq_iSup_nnnorm : ‖f‖₊ = ⨆ x : α, ‖f x‖₊ :=
  (mkOfCompact f).nnnorm_eq_iSup_nnnorm

theorem norm_eq_iSup_norm : ‖f‖ = ⨆ x : α, ‖f x‖ :=
  (mkOfCompact f).norm_eq_iSup_norm

instance {X : Type*} [TopologicalSpace X] (K : TopologicalSpace.Compacts X) :
    CompactSpace (K : Set X) :=
  TopologicalSpace.Compacts.instCompactSpaceSubtypeMem ..

theorem norm_restrict_mono_set {X : Type*} [TopologicalSpace X] (f : C(X, E))
    {K L : TopologicalSpace.Compacts X} (hKL : K ≤ L) : ‖f.restrict K‖ ≤ ‖f.restrict L‖ :=
  (norm_le _ (norm_nonneg _)).mpr fun x => norm_coe_le_norm (f.restrict L) <| Set.inclusion hKL x

end

section

variable {R : Type*}

instance [NonUnitalSeminormedRing R] : NonUnitalSeminormedRing C(α, R) where
  __ : SeminormedAddCommGroup C(α, R) := inferInstance
  __ : NonUnitalRing C(α, R) := inferInstance
  norm_mul f g := norm_mul_le (mkOfCompact f) (mkOfCompact g)

instance [NonUnitalSeminormedCommRing R] : NonUnitalSeminormedCommRing C(α, R) where
  __ : NonUnitalSeminormedRing C(α, R) := inferInstance
  __ : NonUnitalCommRing C(α, R) := inferInstance

instance [SeminormedRing R] : SeminormedRing C(α, R) where
  __ : NonUnitalSeminormedRing C(α, R) := inferInstance
  __ : Ring C(α, R) := inferInstance

instance [SeminormedCommRing R] : SeminormedCommRing C(α, R) where
  __ : SeminormedRing C(α, R) := inferInstance
  __ : CommRing C(α, R) := inferInstance

instance [NonUnitalNormedRing R] : NonUnitalNormedRing C(α, R) where
  __ : NormedAddCommGroup C(α, R) := inferInstance
  __ : NonUnitalSeminormedRing C(α, R) := inferInstance

instance [NonUnitalNormedCommRing R] : NonUnitalNormedCommRing C(α, R) where
  __ : NonUnitalNormedRing C(α, R) := inferInstance
  __ : NonUnitalCommRing C(α, R) := inferInstance

instance [NormedRing R] : NormedRing C(α, R) where
  __ : NormedAddCommGroup C(α, R) := inferInstance
  __ : SeminormedRing C(α, R) := inferInstance

instance [NormedCommRing R] : NormedCommRing C(α, R) where
  __ : NormedRing C(α, R) := inferInstance
  __ : CommRing C(α, R) := inferInstance

end

section

variable {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]

instance normedSpace : NormedSpace 𝕜 C(α, E) where
  norm_smul_le := norm_smul_le

section

variable (α 𝕜 E)

def linearIsometryBoundedOfCompact : C(α, E) ≃ₗᵢ[𝕜] α →ᵇ E :=
  { addEquivBoundedOfCompact α E with
    map_smul' := fun c f => by
      ext
      norm_cast
    norm_map' := fun _ => rfl }

variable {α E}

def evalCLM (x : α) : C(α, E) →L[𝕜] E :=
  (BoundedContinuousFunction.evalCLM 𝕜 x).comp
    (linearIsometryBoundedOfCompact α E 𝕜).toLinearIsometry.toContinuousLinearMap

end

@[simp]
theorem linearIsometryBoundedOfCompact_symm_apply (f : α →ᵇ E) :
    (linearIsometryBoundedOfCompact α E 𝕜).symm f = f.toContinuousMap :=
  rfl

@[simp]
theorem linearIsometryBoundedOfCompact_apply_apply (f : C(α, E)) (a : α) :
    (linearIsometryBoundedOfCompact α E 𝕜 f) a = f a :=
  rfl

@[simp]
theorem linearIsometryBoundedOfCompact_toIsometryEquiv :
    (linearIsometryBoundedOfCompact α E 𝕜).toIsometryEquiv = isometryEquivBoundedOfCompact α E :=
  rfl

@[simp]
theorem linearIsometryBoundedOfCompact_toAddEquiv :
    ((linearIsometryBoundedOfCompact α E 𝕜).toLinearEquiv : C(α, E) ≃+ (α →ᵇ E)) =
      addEquivBoundedOfCompact α E :=
  rfl

@[simp]
theorem linearIsometryBoundedOfCompact_of_compact_toEquiv :
    (linearIsometryBoundedOfCompact α E 𝕜).toLinearEquiv.toEquiv = equivBoundedOfCompact α E :=
  rfl

end

@[simp] lemma nnnorm_smul_const {R β : Type*} [NormedAddCommGroup β] [NormedDivisionRing R]
    [Module R β] [BoundedSMul R β] (f : C(α, R)) (b : β) :
    ‖f • const α b‖₊ = ‖f‖₊ * ‖b‖₊ := by
  simp only [nnnorm_eq_iSup_nnnorm, smul_apply', const_apply, nnnorm_smul, iSup_mul]

@[simp] lemma norm_smul_const {R β : Type*} [NormedAddCommGroup β] [NormedDivisionRing R]
    [Module R β] [BoundedSMul R β] (f : C(α, R)) (b : β) :
    ‖f • const α b‖ = ‖f‖ * ‖b‖ := by
  simp only [← coe_nnnorm, NNReal.coe_mul, nnnorm_smul_const]

section

variable {𝕜 : Type*} {γ : Type*} [NormedField 𝕜] [SeminormedRing γ] [NormedAlgebra 𝕜 γ]

instance : NormedAlgebra 𝕜 C(α, γ) :=
  { ContinuousMap.normedSpace, ContinuousMap.algebra with }

end

end ContinuousMap

namespace ContinuousMap

section UniformContinuity

variable {α β : Type*}

variable [PseudoMetricSpace α] [CompactSpace α] [PseudoMetricSpace β]

/-!
We now set up some declarations making it convenient to use uniform continuity.
-/

theorem uniform_continuity (f : C(α, β)) (ε : ℝ) (h : 0 < ε) :
    ∃ δ > 0, ∀ {x y}, dist x y < δ → dist (f x) (f y) < ε :=
  Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous f.continuous) ε h

def modulus (f : C(α, β)) (ε : ℝ) (h : 0 < ε) : ℝ :=
  Classical.choose (uniform_continuity f ε h)

theorem modulus_pos (f : C(α, β)) {ε : ℝ} {h : 0 < ε} : 0 < f.modulus ε h :=
  (Classical.choose_spec (uniform_continuity f ε h)).1

theorem dist_lt_of_dist_lt_modulus (f : C(α, β)) (ε : ℝ) (h : 0 < ε) {a b : α}
    (w : dist a b < f.modulus ε h) : dist (f a) (f b) < ε :=
  (Classical.choose_spec (uniform_continuity f ε h)).2 w

end UniformContinuity

end ContinuousMap

section CompLeft

variable (X : Type*) {𝕜 β γ : Type*} [TopologicalSpace X] [CompactSpace X]
  [NontriviallyNormedField 𝕜]

variable [SeminormedAddCommGroup β] [NormedSpace 𝕜 β] [SeminormedAddCommGroup γ] [NormedSpace 𝕜 γ]

open ContinuousMap

protected def ContinuousLinearMap.compLeftContinuousCompact (g : β →L[𝕜] γ) :
    C(X, β) →L[𝕜] C(X, γ) :=
  (linearIsometryBoundedOfCompact X γ 𝕜).symm.toLinearIsometry.toContinuousLinearMap.comp <|
    (g.compLeftContinuousBounded X).comp <|
      (linearIsometryBoundedOfCompact X β 𝕜).toLinearIsometry.toContinuousLinearMap

@[simp]
theorem ContinuousLinearMap.toLinear_compLeftContinuousCompact (g : β →L[𝕜] γ) :
    (g.compLeftContinuousCompact X : C(X, β) →ₗ[𝕜] C(X, γ)) = g.compLeftContinuous 𝕜 X := by
  ext f
  rfl

@[simp]
theorem ContinuousLinearMap.compLeftContinuousCompact_apply (g : β →L[𝕜] γ) (f : C(X, β)) (x : X) :
    g.compLeftContinuousCompact X f x = g (f x) :=
  rfl

end CompLeft

namespace ContinuousMap

section LocalNormalConvergence

/-! ### Local normal convergence

A sum of continuous functions (on a locally compact space) is "locally normally convergent" if the
sum of its sup-norms on any compact subset is summable. This implies convergence in the topology
of `C(X, E)` (i.e. locally uniform convergence). -/

open TopologicalSpace

variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X]

variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]

theorem summable_of_locally_summable_norm {ι : Type*} {F : ι → C(X, E)}
    (hF : ∀ K : Compacts X, Summable fun i => ‖(F i).restrict K‖) : Summable F := by
  classical
  refine (ContinuousMap.exists_tendsto_compactOpen_iff_forall _).2 fun K hK => ?_
  lift K to Compacts X using hK
  have A : ∀ s : Finset ι, restrict (↑K) (∑ i ∈ s, F i) = ∑ i ∈ s, restrict K (F i) := by
    intro s
    ext1 x
    simp
    -- This used to be the end of the proof before https://github.com/leanprover/lean4/pull/2644
    erw [restrict_apply, restrict_apply, restrict_apply, restrict_apply]
    simp? says simp only [coe_sum, Finset.sum_apply]
    congr!
  simpa only [HasSum, A] using (hF K).of_norm

end LocalNormalConvergence

/-!
### Star structures

In this section, if `β` is a normed ⋆-group, then so is the space of
continuous functions from `α` to `β`, by using the star operation pointwise.

Furthermore, if `α` is compact and `β` is a C⋆-ring, then `C(α, β)` is a C⋆-ring. -/

section NormedSpace

variable {α : Type*} {β : Type*}

variable [TopologicalSpace α] [SeminormedAddCommGroup β] [StarAddMonoid β] [NormedStarGroup β]

theorem _root_.BoundedContinuousFunction.mkOfCompact_star [CompactSpace α] (f : C(α, β)) :
    mkOfCompact (star f) = star (mkOfCompact f) :=
  rfl

instance [CompactSpace α] : NormedStarGroup C(α, β) where
  norm_star f := by
    rw [← BoundedContinuousFunction.norm_mkOfCompact, BoundedContinuousFunction.mkOfCompact_star,
      norm_star, BoundedContinuousFunction.norm_mkOfCompact]

end NormedSpace

section CStarRing

variable {α : Type*} {β : Type*}

variable [TopologicalSpace α] [CompactSpace α]

instance [NonUnitalNormedRing β] [StarRing β] [CStarRing β] : CStarRing C(α, β) where
  norm_mul_self_le f := by
    rw [← sq, ← Real.le_sqrt (norm_nonneg _) (norm_nonneg _),
      ContinuousMap.norm_le _ (Real.sqrt_nonneg _)]
    intro x
    rw [Real.le_sqrt (norm_nonneg _) (norm_nonneg _), sq, ← CStarRing.norm_star_mul_self]
    exact ContinuousMap.norm_coe_le_norm (star f * f) x

end CStarRing

end ContinuousMap
