/-
Extracted from Topology/Algebra/LinearTopology.lean
Genuine: 17 of 24 | Dissolved: 3 | Infrastructure: 4
-/
import Origin.Core

/-! # Linear topologies on modules and rings

Let `M` be a (left) module over a ring `R`. Following
[Stacks: Definition 15.36.1](https://stacks.math.columbia.edu/tag/07E8), we say that a
topology on `M` is *`R`-linear* if it is invariant by translations and admits a basis of
neighborhoods of 0 consisting of (left) `R`-submodules.

If `M` is an `(R, R')`-bimodule, we show that a topology is both `R`-linear and `R'`-linear
if and only if there exists a basis of neighborhoods of 0 consisting of `(R, R')`-subbimodules.

In particular, we say that a topology on the ring `R` is *linear* if it is linear if
it is linear when `R` is viewed as an `(R, Rᵐᵒᵖ)`-bimodule. By the previous results,
this means that there exists a basis of neighborhoods of 0 consisting of two-sided ideals,
hence our definition agrees with [N. Bourbaki, *Algebra II*, chapter 4, §2, n° 3][bourbaki1981].

## Main definitions and statements

* `IsLinearTopology R M`: the topology on `M` is `R`-linear, meaning that there exists a basis
  of neighborhoods of 0 consisting of `R`-submodules. Note that we don't impose that the topology
  is invariant by translation, so you'll often want to add `ContinuousConstVAdd M M` to get
  something meaningful. To express that the topology of a ring `R` is linear, use
  `[IsLinearTopology R R] [IsLinearTopology Rᵐᵒᵖ R]`.
* `IsLinearTopology.mk_of_hasBasis`: a convenient constructor for `IsLinearTopology`.
  See also `IsLinearTopology.mk_of_hasBasis'`.
* The discrete topology on `M` is `R`-linear (declared as an `instance`).
* `IsLinearTopology.hasBasis_subbimodule`: assume that `M` is an `(R, R')`-bimodule,
  and that its topology is both `R`-linear and `R'`-linear. Then there exists a basis of
  neighborhoods of 0 made of `(R, R')`-subbimodules. Note that this is not trivial, since the bases
  witnessing `R`-linearity and `R'`-linearity may have nothing to do with each other
* `IsLinearTopology.tendsto_smul_zero`: assume that the topology on `M` is linear.
  For `m : ι → M` such that `m i` tends to 0, `r i • m i` still tends to 0 for any `r : ι → R`.

* `IsLinearTopology.hasBasis_twoSidedIdeal`: if the ring `R` is linearly topologized,
  in the sense that we have both `IsLinearTopology R R` and `IsLinearTopology Rᵐᵒᵖ R`,
  then there exists a basis of neighborhoods of 0 consisting of two-sided ideals.
* Conversely, to prove `IsLinearTopology R R` and `IsLinearTopology Rᵐᵒᵖ R`
  from a basis of two-sided ideals, use `IsLinearTopology.mk_of_hasBasis'` twice.
* `IsLinearTopology.tendsto_mul_zero_of_left`: assume that the topology on `R` is (right-)linear.
  For `f, g : ι → R` such that `f i` tends to `0`, `f i * g i` still tends to `0`.
* `IsLinearTopology.tendsto_mul_zero_of_right`: assume that the topology on `R` is (left-)linear.
  For `f, g : ι → R` such that `g i` tends to `0`, `f i * g i` still tends to `0`
* If `R` is a commutative ring and its topology is left-linear, it is automatically
  right-linear (declared as a low-priority instance).

## Notes on the implementation

* Some statements assume `ContinuousAdd M` where `ContinuousConstVAdd M M`
  (invariance by translation) would be enough. In fact, in presence of `IsLinearTopology R M`,
  invariance by translation implies that `M` is a topological additive group on which `R` acts
  by homeomorphisms. Similarly, `IsLinearTopology R R` and `ContinuousConstVAdd R R` imply that
  `R` is a topological ring. All of this will follow from https://github.com/leanprover-community/mathlib4/issues/18437.

  Nevertheless, we don't plan on adding those facts as instances: one should use directly
  results from https://github.com/leanprover-community/mathlib4/issues/18437 to get `IsTopologicalAddGroup` and `IsTopologicalRing` instances.

* The main constructor for `IsLinearTopology`, `IsLinearTopology.mk_of_hasBasis`
  is formulated in terms of the subobject classes `AddSubmonoidClass` and `SMulMemClass`
  to allow for more complicated types than `Submodule R M` or `Ideal R`. Unfortunately, the scalar
  ring in `SMulMemClass` is an `outParam`, which means that Lean only considers one base ring for
  a given subobject type. For example, Lean will *never* find `SMulMemClass (TwoSidedIdeal R) R R`
  because it prioritizes the (later-defined) instance of `SMulMemClass (TwoSidedIdeal R) Rᵐᵒᵖ R`.

  This makes `IsLinearTopology.mk_of_hasBasis` un-applicable to `TwoSidedIdeal` (and probably other
  types), thus we provide `IsLinearTopology.mk_of_hasBasis'` as an alternative not relying on
  typeclass inference.
-/

open scoped Topology

open Filter

namespace IsLinearTopology

section Module

variable {R R' M : Type*} [Ring R] [Ring R'] [AddCommGroup M] [Module R M] [Module R' M]
  [SMulCommClass R R' M] [TopologicalSpace M]

variable (R M) in

class _root_.IsLinearTopology where
  hasBasis_submodule' : (𝓝 (0 : M)).HasBasis
    (fun N : Submodule R M ↦ (N : Set M) ∈ 𝓝 0) (fun N : Submodule R M ↦ (N : Set M))

variable (R) in

lemma hasBasis_submodule [IsLinearTopology R M] : (𝓝 (0 : M)).HasBasis
    (fun N : Submodule R M ↦ (N : Set M) ∈ 𝓝 0) (fun N : Submodule R M ↦ (N : Set M)) :=
  IsLinearTopology.hasBasis_submodule'

variable (R) in

lemma hasBasis_open_submodule [ContinuousAdd M] [IsLinearTopology R M] :
    (𝓝 (0 : M)).HasBasis
      (fun N : Submodule R M ↦ IsOpen (N : Set M)) (fun N : Submodule R M ↦ (N : Set M)) :=
  hasBasis_submodule R |>.congr
    (fun N ↦ ⟨N.toAddSubgroup.isOpen_of_mem_nhds, fun hN ↦ hN.mem_nhds (zero_mem N)⟩)
    (fun _ _ ↦ rfl)

variable (R) in

variable (R) in

lemma mk_of_hasBasis {ι : Sort*} {S : Type*} [SetLike S M]
    [SMulMemClass S R M] [AddSubmonoidClass S M]
    {p : ι → Prop} {s : ι → S}
    (h : (𝓝 0).HasBasis p (fun i ↦ (s i : Set M))) :
    IsLinearTopology R M :=
  mk_of_hasBasis' R h fun _ ↦ SMulMemClass.smul_mem

theorem _root_.isLinearTopology_iff_hasBasis_submodule :
    IsLinearTopology R M ↔ (𝓝 0).HasBasis
      (fun N : Submodule R M ↦ (N : Set M) ∈ 𝓝 0) (fun N : Submodule R M ↦ (N : Set M)) :=
  ⟨fun _ ↦ hasBasis_submodule R, fun h ↦ .mk_of_hasBasis R h⟩

theorem _root_.isLinearTopology_iff_hasBasis_open_submodule [ContinuousAdd M] :
    IsLinearTopology R M ↔ (𝓝 0).HasBasis
      (fun N : Submodule R M ↦ IsOpen (N : Set M)) (fun N : Submodule R M ↦ (N : Set M)) :=
  ⟨fun _ ↦ hasBasis_open_submodule R, fun h ↦ .mk_of_hasBasis R h⟩

-- INSTANCE (free from Core): [DiscreteTopology

variable (R R') in

open Set Pointwise in

variable (R R') in

open Set Pointwise in

lemma hasBasis_open_subbimodule [ContinuousAdd M] [IsLinearTopology R M] [IsLinearTopology R' M] :
    (𝓝 (0 : M)).HasBasis
      (fun I : AddSubgroup M ↦ IsOpen (I : Set M) ∧
        (∀ r : R, ∀ x ∈ I, r • x ∈ I) ∧ (∀ r' : R', ∀ x ∈ I, r' • x ∈ I))
      (fun I : AddSubgroup M ↦ (I : Set M)) :=
  hasBasis_subbimodule R R' |>.congr
    (fun N ↦ and_congr_left' ⟨N.isOpen_of_mem_nhds, fun hN ↦ hN.mem_nhds (zero_mem N)⟩)
    (fun _ _ ↦ rfl)

variable (R) in

-- DISSOLVED: tendsto_smul_zero

variable (R) in

theorem _root_.IsCentralScalar.isLinearTopology_iff [Module Rᵐᵒᵖ M] [IsCentralScalar R M] :
    IsLinearTopology Rᵐᵒᵖ M ↔ IsLinearTopology R M := by
  constructor <;> intro H
  · exact mk_of_hasBasis' R (IsLinearTopology.hasBasis_submodule Rᵐᵒᵖ)
      fun S r m hm ↦ op_smul_eq_smul r m ▸ S.smul_mem _ hm
  · exact mk_of_hasBasis' Rᵐᵒᵖ (IsLinearTopology.hasBasis_submodule R)
      fun S r m hm ↦ unop_smul_eq_smul r m ▸ S.smul_mem _ hm

end Module

section Ring

variable {R : Type*} [Ring R] [TopologicalSpace R]

theorem hasBasis_ideal [IsLinearTopology R R] :
    (𝓝 0).HasBasis (fun I : Ideal R ↦ (I : Set R) ∈ 𝓝 0) (fun I : Ideal R ↦ (I : Set R)) :=
  hasBasis_submodule R

theorem hasBasis_open_ideal [ContinuousAdd R] [IsLinearTopology R R] :
    (𝓝 0).HasBasis (fun I : Ideal R ↦ IsOpen (I : Set R)) (fun I : Ideal R ↦ (I : Set R)) :=
  hasBasis_open_submodule R

theorem _root_.isLinearTopology_iff_hasBasis_ideal :
    IsLinearTopology R R ↔ (𝓝 0).HasBasis
      (fun I : Ideal R ↦ (I : Set R) ∈ 𝓝 0) (fun I : Ideal R ↦ (I : Set R)) :=
  isLinearTopology_iff_hasBasis_submodule

theorem _root_.isLinearTopology_iff_hasBasis_open_ideal [IsTopologicalRing R] :
    IsLinearTopology R R ↔ (𝓝 0).HasBasis
      (fun I : Ideal R ↦ IsOpen (I : Set R)) (fun I : Ideal R ↦ (I : Set R)) :=
  isLinearTopology_iff_hasBasis_open_submodule

theorem hasBasis_right_ideal [IsLinearTopology Rᵐᵒᵖ R] :
    (𝓝 0).HasBasis (fun I : Submodule Rᵐᵒᵖ R ↦ (I : Set R) ∈ 𝓝 0) (fun I ↦ (I : Set R)) :=
  hasBasis_submodule Rᵐᵒᵖ

open Set Pointwise in

lemma hasBasis_twoSidedIdeal [IsLinearTopology R R] [IsLinearTopology Rᵐᵒᵖ R] :
    (𝓝 (0 : R)).HasBasis (fun I : TwoSidedIdeal R ↦ (I : Set R) ∈ 𝓝 0)
      (fun I : TwoSidedIdeal R ↦ (I : Set R)) :=
  hasBasis_subbimodule R Rᵐᵒᵖ |>.to_hasBasis
    (fun I ⟨hI, hRI, hRI'⟩ ↦ ⟨.mk' I (zero_mem _) add_mem neg_mem (hRI _ _) (hRI' _ _),
      by simpa using hI, by simp⟩)
    (fun I hI ↦ ⟨I.asIdeal.toAddSubgroup,
      ⟨hI, I.mul_mem_left, fun r x hx ↦ I.mul_mem_right x (r.unop) hx⟩, subset_rfl⟩)

lemma hasBasis_open_twoSidedIdeal [ContinuousAdd R]
    [IsLinearTopology R R] [IsLinearTopology Rᵐᵒᵖ R] :
    (𝓝 (0 : R)).HasBasis
      (fun I : TwoSidedIdeal R ↦ IsOpen (I : Set R)) (fun I : TwoSidedIdeal R ↦ (I : Set R)) :=
  hasBasis_twoSidedIdeal.congr
    (fun I ↦ ⟨I.asIdeal.toAddSubgroup.isOpen_of_mem_nhds, fun hI ↦ hI.mem_nhds (zero_mem I)⟩)
    (fun _ _ ↦ rfl)

theorem _root_.isLinearTopology_iff_hasBasis_twoSidedIdeal :
    IsLinearTopology R R ∧ IsLinearTopology Rᵐᵒᵖ R ↔
      (𝓝 0).HasBasis
        (fun I : TwoSidedIdeal R ↦ (I : Set R) ∈ 𝓝 0) (fun I : TwoSidedIdeal R ↦ (I : Set R)) :=
  ⟨fun ⟨_, _⟩ ↦ hasBasis_twoSidedIdeal, fun h ↦
    ⟨.mk_of_hasBasis' R h fun I r x hx ↦ I.mul_mem_left r x hx,
      .mk_of_hasBasis' Rᵐᵒᵖ h fun I r x hx ↦ I.mul_mem_right x r.unop hx⟩⟩

theorem _root_.isLinearTopology_iff_hasBasis_open_twoSidedIdeal [ContinuousAdd R] :
    IsLinearTopology R R ∧ IsLinearTopology Rᵐᵒᵖ R ↔ (𝓝 0).HasBasis
      (fun I : TwoSidedIdeal R ↦ IsOpen (I : Set R)) (fun I : TwoSidedIdeal R ↦ (I : Set R)) :=
  ⟨fun ⟨_, _⟩ ↦ hasBasis_open_twoSidedIdeal, fun h ↦
    ⟨.mk_of_hasBasis' R h fun I r x hx ↦ I.mul_mem_left r x hx,
      .mk_of_hasBasis' Rᵐᵒᵖ h fun I r x hx ↦ I.mul_mem_right x r.unop hx⟩⟩

-- DISSOLVED: tendsto_mul_zero_of_left

-- DISSOLVED: tendsto_mul_zero_of_right

end Ring

section CommRing

variable {R M : Type*} [CommRing R] [TopologicalSpace R]

-- INSTANCE (free from Core): (priority

end CommRing

end IsLinearTopology
