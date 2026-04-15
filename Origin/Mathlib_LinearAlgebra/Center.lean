/-
Extracted from LinearAlgebra/Center.lean
Genuine: 3 of 4 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Center of the algebra of linear endomorphisms

If `V` is an `R`-module, we say that an endomorphism `f : Module.End R V`
is a *homothety* with central ratio if there exists `a ∈ Set.center R`
such that `f x = a • x` for all `x`.
By `Module.End.mem_subsemiringCenter_iff`, these linear maps constitute
the center of `Module.End R V`.
(When `R` is commutative, we can write `f = a • LinearMap.id`.)

In what follows, `V` is assumed to be a free `R`-module.

* `LinearMap.commute_transvections_iff_of_basis`:
  if an endomorphism `f : V →ₗ[R] V` commutes with every elementary transvection
  (in a given basis), then it is a homothety with central ratio.
  (Assumes that the basis is provided and has a non trivial set of indices.)

* `LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent`:
  over a commutative ring `R` which is a domain, an endomorphism `f : V →ₗ[R] V`
  of a free module such that `v` and `f v` are not linearly independent,
  for all `v : V`, is a homothety.

* `LinearMap.exists_mem_center_apply_eq_smul_of_forall_notLinearIndependent`:
  a variant that does not assume that `R` is commutative.
  Then the homothety has central ratio.

* `LinearMap.exists_mem_center_apply_eq_smul_of_forall_notLinearIndependent_of_basis`:
  a variant that does not assume that `R` has the strong rank condition,
  but requires a basis.

Note. In the noncommutative case, the last two results do not hold
when the rank is equal to 1. Indeed, right multiplications
with noncentral ratio of the `R`-module `R` satisfy the property
that `f v` and `v` are linearly dependent, for all `v : V`,
but they are not left multiplication by some element.

-/

open Module LinearMap LinearEquiv Set Finsupp

namespace LinearMap

variable {R V : Type*}

set_option backward.isDefEq.respectTransparency false in

theorem commute_transvections_iff_of_basis
    [Ring R] [AddCommGroup V] [Module R V]
    {ι : Type*} [Nontrivial ι] (b : Basis ι R V)
    {f : V →ₗ[R] V}
    (hcomm : ∀ i j (r : R) (_ : i ≠ j), Commute f (transvection (b.coord i) (r • b j))) :
    ∃ a : Subring.center R, f = a • 1 := by
  simp only [SetLike.exists, Subring.mem_center_iff]
  rcases subsingleton_or_nontrivial V with hV | hV
  · refine ⟨1, by simp, ?_⟩
    ext x
    simp [Subring.smul_def, hV.allEq (f x) x]
  simp only [commute_iff_eq] at hcomm
  replace hcomm (i j : ι) (hij : i ≠ j) (r : R) :
      r • f (b j) = b.coord i (f (b i)) • r • b j := by
    have := hcomm i j r hij
    rw [LinearMap.ext_iff] at this
    simpa [LinearMap.transvection.apply] using this (b i)
  have h_allEq (i j : ι) : b.coord i (f (b i)) = b.coord j (f (b j)) := by
    by_cases hij : j = i
    · simp [hij]
    simpa using congr_arg (b.coord i) (hcomm j i hij 1)
  replace hcomm (i : ι) (r : R) : r • f (b i) = b.coord i (f (b i)) • r • b i := by
    obtain ⟨j, hji⟩ := exists_ne i
    simpa [h_allEq j i] using hcomm j i hji r
  let i : ι := Classical.ofNonempty
  refine ⟨b.coord i (f (b i)), fun r ↦ by simpa using congr(b.coord i $(hcomm i r)), ?_⟩
  ext x
  rw [← b.linearCombination_repr x, linearCombination_apply, map_finsuppSum]
  simp only [smul_apply, End.one_apply, smul_sum]
  apply sum_congr
  intro j _
  simp [Subring.smul_def, h_allEq i j, hcomm j]

set_option backward.isDefEq.respectTransparency false in

set_option backward.isDefEq.respectTransparency false in

theorem exists_mem_center_apply_eq_smul_of_forall_notLinearIndependent
    [Ring R] [IsDomain R] [StrongRankCondition R]
    [AddCommGroup V] [Module R V] [Free R V]
    {f : V →ₗ[R] V}
    (hV1 : finrank R V ≠ 1)
    (h : ∀ v, ¬ LinearIndependent R ![v, f v]) :
    ∃ a : Subring.center R, f = a • 1 := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · use 1
    ext x
    apply hV.allEq
  let ι := Free.ChooseBasisIndex R V
  let b : Basis ι R V := Free.chooseBasis R V
  rcases subsingleton_or_nontrivial ι with hι | hι
  · have : Nonempty ι := Free.instNonemptyChooseBasisIndexOfNontrivial R V
    have : Fintype ι := Fintype.ofFinite ι
    simp_all [finrank_eq_card_basis b, ← Nat.card_eq_fintype_card]
  exact exists_mem_center_apply_eq_smul_of_forall_notLinearIndependent_of_basis b h

theorem exists_eq_smul_id_of_forall_notLinearIndependent
    [CommRing R] [IsDomain R] [AddCommGroup V] [Module R V] [Free R V] {f : V →ₗ[R] V}
    (h : ∀ v, ¬ LinearIndependent R ![v, f v]) :
    ∃ a : R, f = a • 1 := by
  by_cases hV1 : finrank R V = 1
  · rw [finrank_eq_one_iff Unit] at hV1
    let b : Basis Unit R V := Classical.ofNonempty
    use b.coord () (f (b ()))
    apply b.ext
    intro i
    nth_rewrite 1 [← b.linearCombination_repr (f (b i))]
    simp [linearCombination_unique]
  obtain ⟨a, rfl⟩ := exists_mem_center_apply_eq_smul_of_forall_notLinearIndependent hV1 h
  refine ⟨a, by simp [Subring.smul_def]⟩

end LinearMap
