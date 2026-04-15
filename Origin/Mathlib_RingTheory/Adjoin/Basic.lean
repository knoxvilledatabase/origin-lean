/-
Extracted from RingTheory/Adjoin/Basic.lean
Genuine: 6 of 6 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Adjoining elements to form subalgebras

This file contains basic results on `Algebra.adjoin`.

## Tags

adjoin, algebra

-/

assert_not_exists Polynomial

universe uR uS uA uB

open Module Submodule Subsemiring

open scoped Pointwise

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

namespace Algebra

section Semiring

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra R A] [Algebra S A] [Algebra R B] [IsScalarTower R S A]

variable {s t : Set A}

variable (R A)

variable {A} (s)

theorem adjoin_prod_le (s : Set A) (t : Set B) :
    adjoin R (s ×ˢ t) ≤ (adjoin R s).prod (adjoin R t) :=
  adjoin_le <| Set.prod_mono subset_adjoin subset_adjoin

theorem adjoin_inl_union_inr_eq_prod (s) (t) :
    adjoin R (LinearMap.inl R A B '' (s ∪ {1}) ∪ LinearMap.inr R A B '' (t ∪ {1})) =
      (adjoin R s).prod (adjoin R t) := by
  apply le_antisymm
  · simp only [adjoin_le_iff, Set.insert_subset_iff, Subalgebra.zero_mem, Subalgebra.one_mem,
      subset_adjoin, -- the rest comes from `squeeze_simp`
      Set.union_subset_iff,
      LinearMap.coe_inl, Set.mk_preimage_prod_right, Set.image_subset_iff, SetLike.mem_coe,
      Set.mk_preimage_prod_left, LinearMap.coe_inr, and_self_iff, Set.union_singleton,
      Subalgebra.coe_prod]
  · rintro ⟨a, b⟩ ⟨ha, hb⟩
    let P := adjoin R (LinearMap.inl R A B '' (s ∪ {1}) ∪ LinearMap.inr R A B '' (t ∪ {1}))
    have Ha : (a, (0 : B)) ∈ adjoin R (LinearMap.inl R A B '' (s ∪ {1})) :=
      mem_adjoin_of_map_mul R LinearMap.inl_map_mul ha
    have Hb : ((0 : A), b) ∈ adjoin R (LinearMap.inr R A B '' (t ∪ {1})) :=
      mem_adjoin_of_map_mul R LinearMap.inr_map_mul hb
    replace Ha : (a, (0 : B)) ∈ P := adjoin_mono Set.subset_union_left Ha
    replace Hb : ((0 : A), b) ∈ P := adjoin_mono Set.subset_union_right Hb
    simpa [P] using Subalgebra.add_mem _ Ha Hb

variable (A) in

theorem adjoin_algebraMap (s : Set S) :
    adjoin R (algebraMap S A '' s) = (adjoin R s).map (IsScalarTower.toAlgHom R S A) :=
  adjoin_image R (IsScalarTower.toAlgHom R S A) s

theorem adjoin_algebraMap_image_union_eq_adjoin_adjoin (s : Set S) (t : Set A) :
    adjoin R (algebraMap S A '' s ∪ t) = (adjoin (adjoin R s) t).restrictScalars R :=
  le_antisymm
    (closure_mono <|
      Set.union_subset (Set.range_subset_iff.2 fun r => Or.inl ⟨algebraMap R (adjoin R s) r,
        (IsScalarTower.algebraMap_apply _ _ _ _).symm⟩)
        (Set.union_subset_union_left _ fun _ ⟨_x, hx, hxs⟩ => hxs ▸ ⟨⟨_, subset_adjoin hx⟩, rfl⟩))
    (closure_le.2 <|
      Set.union_subset (Set.range_subset_iff.2 fun x => adjoin_mono Set.subset_union_left <|
        Algebra.adjoin_algebraMap R A s ▸ ⟨x, x.prop, rfl⟩)
        (Set.Subset.trans Set.subset_union_right subset_adjoin))

theorem adjoin_adjoin_of_tower (s : Set A) : adjoin S (adjoin R s : Set A) = adjoin S s := by
  apply le_antisymm (adjoin_le _)
  · exact adjoin_mono subset_adjoin
  · rw [← Subalgebra.coe_restrictScalars R (S := S), SetLike.coe_subset_coe]
    exact adjoin_le subset_adjoin

theorem Subalgebra.restrictScalars_adjoin {s : Set A} :
    (adjoin S s).restrictScalars R = (IsScalarTower.toAlgHom R S A).range ⊔ adjoin R s := by
  refine le_antisymm (fun _ hx ↦ adjoin_induction
    (fun x hx ↦ le_sup_right (α := Subalgebra R A) (subset_adjoin hx))
    (fun x ↦ le_sup_left (α := Subalgebra R A) ⟨x, rfl⟩)
    (fun _ _ _ _ ↦ add_mem) (fun _ _ _ _ ↦ mul_mem) <|
    (Subalgebra.mem_restrictScalars _).mp hx) (sup_le ?_ <| adjoin_le subset_adjoin)
  rintro _ ⟨x, rfl⟩; exact algebraMap_mem (adjoin S s) x
