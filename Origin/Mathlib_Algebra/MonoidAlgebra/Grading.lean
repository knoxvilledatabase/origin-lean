/-
Extracted from Algebra/MonoidAlgebra/Grading.lean
Genuine: 10 of 15 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-!
# Internal grading of an `AddMonoidAlgebra`

In this file, we show that an `AddMonoidAlgebra` has an internal direct sum structure.

## Main results

* `AddMonoidAlgebra.gradeBy R f i`: the `i`th grade of an `R[M]` given by the
  degree function `f`.
* `AddMonoidAlgebra.grade R i`: the `i`th grade of an `R[M]` when the degree
  function is the identity.
* `AddMonoidAlgebra.gradeBy.gradedAlgebra`: `AddMonoidAlgebra` is an algebra graded by
  `AddMonoidAlgebra.gradeBy`.
* `AddMonoidAlgebra.grade.gradedAlgebra`: `AddMonoidAlgebra` is an algebra graded by
  `AddMonoidAlgebra.grade`.
* `AddMonoidAlgebra.gradeBy.isInternal`: propositionally, the statement that
  `AddMonoidAlgebra.gradeBy` defines an internal graded structure.
* `AddMonoidAlgebra.grade.isInternal`: propositionally, the statement that
  `AddMonoidAlgebra.grade` defines an internal graded structure when the degree function
  is the identity.
-/

noncomputable section

namespace AddMonoidAlgebra

variable {M : Type*} {ι : Type*} {R : Type*}

variable (R) [CommSemiring R]

abbrev gradeBy (f : M → ι) (i : ι) : Submodule R R[M] where
  carrier := { a | ∀ m, m ∈ a.support → f m = i }
  zero_mem' m h := by cases h
  add_mem' {a b} ha hb m h := by
    classical exact (Finset.mem_union.mp (Finsupp.support_add h)).elim (ha m) (hb m)
  smul_mem' _ _ h := Set.Subset.trans Finsupp.support_smul h

abbrev grade (m : M) : Submodule R R[M] :=
  gradeBy R id m

theorem mem_grade_iff (m : M) (a : R[M]) : a ∈ grade R m ↔ a.support ⊆ {m} := by
  rw [← Finset.coe_subset, Finset.coe_singleton]
  rfl

theorem mem_grade_iff' (m : M) (a : R[M]) :
    a ∈ grade R m ↔ a ∈ (LinearMap.range (Finsupp.lsingle m : R →ₗ[R] M →₀ R) :
      Submodule R R[M]) := by
  rw [mem_grade_iff, Finsupp.support_subset_singleton']
  apply exists_congr
  intro r
  constructor <;> exact Eq.symm

theorem grade_eq_lsingle_range (m : M) :
    grade R m = LinearMap.range (Finsupp.lsingle m : R →ₗ[R] M →₀ R) :=
  Submodule.ext (mem_grade_iff' R m)

theorem single_mem_gradeBy {R} [CommSemiring R] (f : M → ι) (m : M) (r : R) :
    single m r ∈ gradeBy R f (f m) := by
  intro x hx
  rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hx)]

theorem single_mem_grade {R} [CommSemiring R] (i : M) (r : R) :
    single i r ∈ grade R i :=
  single_mem_gradeBy _ _ _

end

open DirectSum

-- INSTANCE (free from Core): gradeBy.gradedMonoid

-- INSTANCE (free from Core): grade.gradedMonoid

variable [AddMonoid M] [DecidableEq ι] [AddMonoid ι] [CommSemiring R] (f : M →+ ι)

set_option backward.isDefEq.respectTransparency false in

def decomposeAux : R[M] →ₐ[R] ⨁ i : ι, gradeBy R f i :=
  AddMonoidAlgebra.lift R _ M
    { toFun := fun m =>
        DirectSum.of (fun i : ι => gradeBy R f i) (f m.toAdd)
          ⟨Finsupp.single m.toAdd 1, single_mem_gradeBy _ _ _⟩
      map_one' :=
        DirectSum.of_eq_of_gradedMonoid_eq
          (by congr 2 <;> simp)
      map_mul' := fun i j => by
        symm
        dsimp +instances only [toAdd_one, Eq.ndrec, Set.mem_setOf_eq, ne_eq, OneHom.toFun_eq_coe,
          OneHom.coe_mk, toAdd_mul]
        convert DirectSum.of_mul_of (A := (fun i : ι => gradeBy R f i)) _ _
        repeat { rw [map_add] }
        simp only [SetLike.coe_gMul]
        exact Eq.trans (by rw [one_mul]) (single_mul_single ..).symm }

theorem decomposeAux_single (m : M) (r : R) :
    decomposeAux f (Finsupp.single m r) =
      DirectSum.of (fun i : ι => gradeBy R f i) (f m)
        ⟨Finsupp.single m r, single_mem_gradeBy _ _ _⟩ := by
  refine (lift_single _ _ _).trans ?_
  refine (DirectSum.of_smul R _ _ _).symm.trans ?_
  apply DirectSum.of_eq_of_gradedMonoid_eq
  refine Sigma.subtype_ext rfl ?_
  refine (smul_single' _ _ _).trans ?_
  rw [mul_one]
  rfl

set_option backward.isDefEq.respectTransparency false in

theorem decomposeAux_coe {i : ι} (x : gradeBy R f i) :
    decomposeAux f ↑x = DirectSum.of (fun i => gradeBy R f i) i x := by
  classical
  obtain ⟨x, hx⟩ := x
  revert hx
  refine Finsupp.induction x ?_ ?_
  · intro hx
    symm
    exact map_zero _
  · intro m b y hmy hb ih hmby
    have : Disjoint (Finsupp.single m b).support y.support := by
      simpa only [Finsupp.support_single_ne_zero _ hb, Finset.disjoint_singleton_left]
    rw [mem_gradeBy_iff, Finsupp.support_add_eq this, Finset.coe_union, Set.union_subset_iff]
      at hmby
    obtain ⟨h1, h2⟩ := hmby
    have : f m = i := by
      rwa [Finsupp.support_single_ne_zero _ hb, Finset.coe_singleton, Set.singleton_subset_iff]
        at h1
    subst this
    simp only [map_add, decomposeAux_single f m]
    let ih' := ih h2
    dsimp at ih'
    rw [ih', ← map_add]
    apply DirectSum.of_eq_of_gradedMonoid_eq
    congr 2

-- INSTANCE (free from Core): gradeBy.gradedAlgebra
