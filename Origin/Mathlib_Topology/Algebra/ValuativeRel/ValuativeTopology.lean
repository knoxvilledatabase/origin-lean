/-
Extracted from Topology/Algebra/ValuativeRel/ValuativeTopology.lean
Genuine: 19 of 41 | Dissolved: 15 | Infrastructure: 7
-/
import Origin.Core

/-!
# The topology on a ring induced by a valuation

In this file, we define the non-Archimedean topology induced by a valuation on a ring.

## Main definitions

* If we have both `[ValuativeRel R]` and `[TopologicalSpace R]`, then writing
  `[IsValuativeTopology R]` ensures that the topology on `R` agrees with the one induced by the
  valuation.
* `ValuativeRel.uniformSpace`: The uniform structure introduced by a `ValuativeRel`.

*NOTE* (2026-03-17): The `Valued` instance on a ring `R` would be
replaced by `[ValuativeRel R] [UniformSpace R] [IsValuativeTopology R] [IsUniformAddGroup R]`
(or `[ValuativeRel R] [TopologicalSpace R] [IsValuativeTopology R]` when the uniformity is
not relevant). Additional input `(v : Valuation R Γ₀) [v.Compatible]` can be introduced whenever
a specific compatible valuation is chosen.

The canonical way to introduce the topological structure from a chosen valuation is:
1. First define the `ValuativeRel` structure using `ValuativeRel.ofValuation`;
2. Then define the `UniformSpace` structure using `ValuativeRel.uniformSpace`.
-/

open scoped Topology Uniformity

open Set Filter Valuation ValuativeRel MonoidWithZeroHom ValueGroup₀ ValueGroupWithZero

noncomputable section

variable (R : Type*) [CommRing R] [ValuativeRel R]

variable {R} in

-- DISSOLVED: Valuation.exists_setOf_restrict_le_iff

-- DISSOLVED: IsValuativeTopology

namespace ValuativeRel

-- INSTANCE (free from Core): topologicalSpace

-- INSTANCE (free from Core): nonarchimedeanRing

-- INSTANCE (free from Core): isValuativeTopology

-- INSTANCE (free from Core): uniformSpace

-- INSTANCE (free from Core): isUniformAddGroup

end ValuativeRel

variable {R}

variable {K : Type*} [Field K] [ValuativeRel K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

section TopologicalSpace

variable [TopologicalSpace R] [IsValuativeTopology R] (v : Valuation R Γ₀) [v.Compatible]

namespace IsValuativeTopology

-- DISSOLVED: mem_nhds_iff'

-- DISSOLVED: mem_nhds_zero_iff

-- DISSOLVED: hasBasis_nhds

-- DISSOLVED: hasBasis_nhds'

variable (R) in

-- DISSOLVED: hasBasis_nhds_zero

variable (R) in

-- DISSOLVED: hasBasis_nhds_zero'

end IsValuativeTopology

open IsValuativeTopology

namespace Valuation

lemma mem_nhds_iff {s : Set R} {x : R} : s ∈ 𝓝 x ↔
    ∃ γ : (MonoidWithZeroHom.ValueGroup₀ v)ˣ, { z | v.restrict (z - x) < γ.val } ⊆ s := by
  convert IsValuativeTopology.mem_nhds_iff (s := s) using 4
  simpa [neg_add_eq_sub] using v.exists_setOf_restrict_le_iff _ _

lemma mem_nhds_zero_iff (s : Set R) : s ∈ 𝓝 0 ↔
    ∃ γ : (MonoidWithZeroHom.ValueGroup₀ v)ˣ, { x | v.restrict x < γ.val } ⊆ s := by
  simp [v.mem_nhds_iff]

alias is_topological_valuation := mem_nhds_zero_iff

theorem hasBasis_nhds (x : R) :
    (𝓝 x).HasBasis (fun _ ↦ True)
      fun γ : (MonoidWithZeroHom.ValueGroup₀ v)ˣ ↦ { z | v.restrict (z - x) < γ.val } := by
  simp [Filter.hasBasis_iff, v.mem_nhds_iff]

theorem hasBasis_nhds_zero :
    (𝓝 (0 : R)).HasBasis (fun _ ↦ True)
      fun γ : (MonoidWithZeroHom.ValueGroup₀ v)ˣ ↦ { x | v.restrict x < γ.val } := by
  simp [Filter.hasBasis_iff, v.is_topological_valuation]

-- DISSOLVED: locally_const

end Valuation

namespace IsValuativeTopology

variable (R) in

-- INSTANCE (free from Core): (priority

end IsValuativeTopology

end TopologicalSpace

namespace Valuation

section UniformSpace

variable [_u : UniformSpace R] [IsUniformAddGroup R] [IsValuativeTopology R] (v : Valuation R Γ₀)
  [v.Compatible]

theorem hasBasis_uniformity : (𝓤 R).HasBasis (fun _ ↦ True)
    fun γ : (MonoidWithZeroHom.ValueGroup₀ v)ˣ ↦
      { p : R × R | v.restrict (p.2 - p.1) < γ.1 } := by
  rw [uniformity_eq_comap_nhds_zero]
  exact v.hasBasis_nhds_zero.comap _

theorem toUniformSpace_eq : _u =
    @IsTopologicalAddGroup.rightUniformSpace R _ v.subgroups_basis.topology _ := by
  refine UniformSpace.ext (v.hasBasis_uniformity.eq_of_same_basis ?_)
  convert v.subgroups_basis.hasBasis_nhds_zero.comap _
  simp [restrict_lt_iff_lt_embedding, sub_eq_add_neg]

theorem cauchy_iff {F : Filter R} : Cauchy F ↔
    F.NeBot ∧ ∀ γ : (MonoidWithZeroHom.ValueGroup₀ v)ˣ,
      ∃ M ∈ F, ∀ᵉ (x ∈ M) (y ∈ M), v.restrict (y - x) < γ.1 := by
  rw [v.toUniformSpace_eq, AddGroupFilterBasis.cauchy_iff]
  apply and_congr Iff.rfl
  simp_rw [v.subgroups_basis.mem_addGroupFilterBasis_iff]
  constructor
  · intro h γ
    simp_rw [restrict_lt_iff_lt_embedding]
    exact h _ (v.subgroups_basis.mem_addGroupFilterBasis γ)
  · rintro h - ⟨γ, rfl⟩
    simp_rw [restrict_lt_iff_lt_embedding] at h
    exact h γ

end UniformSpace

section TopologicalSpace

variable [_t : TopologicalSpace R] [IsValuativeTopology R] (v : Valuation R Γ₀) [v.Compatible]
  [TopologicalSpace K] [IsValuativeTopology K]

theorem toTopologicalSpace_eq :
    _t = v.subgroups_basis.topology := by
  letI u := IsTopologicalAddGroup.rightUniformSpace R
  letI := isUniformAddGroup_of_addCommGroup (G := R)
  exact congrArg (fun u ↦ @UniformSpace.toTopologicalSpace R u) v.toUniformSpace_eq

-- INSTANCE (free from Core): (priority

section Discrete

-- DISSOLVED: discreteTopology_of_forall_map_eq_one

-- DISSOLVED: discreteTopology_of_forall_lt

end Discrete

variable {v}

set_option backward.isDefEq.respectTransparency false in

theorem isOpen_ball (r : ValueGroup₀ v) : IsOpen (X := R) {x | v.restrict x < r} := by
  rw [isOpen_iff_mem_nhds]
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  intro x hx
  rw [v.mem_nhds_iff]
  simp only [setOf_subset_setOf]
  exact ⟨Units.mk0 _ hr,
    fun y hy ↦ (sub_add_cancel y x).symm ▸ (v.restrict.map_add _ x).trans_lt (max_lt hy hx)⟩

set_option backward.isDefEq.respectTransparency false in

theorem isClosed_ball (r : ValueGroup₀ v) : IsClosed (X := R) {x | v.restrict x < r} := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  exact AddSubgroup.isClosed_of_isOpen (Valuation.ltAddSubgroup v.restrict (Units.mk0 r hr))
    (isOpen_ball _)

theorem isClopen_ball (r : ValueGroup₀ v) : IsClopen (X := R) {x | v.restrict x < r} :=
  ⟨isClosed_ball _, isOpen_ball _⟩

-- DISSOLVED: isOpen_closedBall

theorem isClosed_closedBall (r : ValueGroup₀ v) : IsClosed (X := R) {x | v.restrict x ≤ r} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  simp only [mem_compl_iff, mem_setOf_eq, not_le] at hx
  rw [v.mem_nhds_iff]
  have hx' : v.restrict x ≠ 0 := ne_of_gt <| lt_of_le_of_lt zero_le' <| hx
  exact ⟨Units.mk0 _ hx', fun y hy hy' ↦ ne_of_lt hy <| map_sub_swap v.restrict x y ▸
      (Valuation.map_sub_eq_of_lt_left _ <| lt_of_le_of_lt hy' hx)⟩

-- DISSOLVED: isClopen_closedBall

-- DISSOLVED: isClopen_sphere

-- DISSOLVED: isOpen_sphere

theorem isClosed_sphere (r : ValueGroup₀ v) : IsClosed (X := R) {x | v.restrict x = r} := by
  rcases eq_or_ne r 0 with rfl | hr
  · convert v.isClosed_closedBall 0 using 3
    exact le_zero_iff.symm
  exact isClopen_sphere hr |>.isClosed

theorem isOpen_integer : IsOpen (v.integer : Set R) := by
  simp only [integer, Subring.coe_set_mk, Subsemiring.coe_set_mk, Submonoid.coe_set_mk,
    Subsemigroup.coe_set_mk, ← v.restrict_le_one_iff]
  apply isOpen_closedBall one_ne_zero

theorem isClosed_integer : IsClosed (v.integer : Set R) := by
  simp only [integer, Subring.coe_set_mk, Subsemiring.coe_set_mk, Submonoid.coe_set_mk,
    Subsemigroup.coe_set_mk, ← v.restrict_le_one_iff]
  exact isClosed_closedBall _

theorem isClopen_integer : IsClopen (v.integer : Set R) :=
  ⟨isClosed_integer, isOpen_integer⟩

theorem isOpen_valuationSubring (v : Valuation K Γ₀) [v.Compatible] :
    IsOpen (v.valuationSubring : Set K) :=
  isOpen_integer

theorem isClosed_valuationSubring (v : Valuation K Γ₀) [v.Compatible] :
    IsClosed (v.valuationSubring : Set K) :=
  isClosed_integer

theorem isClopen_valuationSubring (v : Valuation K Γ₀) [v.Compatible] :
    IsClopen (v.valuationSubring : Set K) :=
  isClopen_integer

end TopologicalSpace

end Valuation

namespace IsValuativeTopology
