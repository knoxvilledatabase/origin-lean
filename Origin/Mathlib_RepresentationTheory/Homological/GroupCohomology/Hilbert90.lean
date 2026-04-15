/-
Extracted from RepresentationTheory/Homological/GroupCohomology/Hilbert90.lean
Genuine: 4 of 7 | Dissolved: 2 | Infrastructure: 1
-/
import Origin.Core

/-!
# Hilbert's Theorem 90

Let `L/K` be a finite extension of fields. Then this file proves Noether's generalization of
Hilbert's Theorem 90: that the 1st group cohomology $H^1(Aut_K(L), L^\times)$ is trivial. We state
it both in terms of $H^1$ and in terms of cocycles being coboundaries.

Hilbert's original statement was that if $L/K$ is Galois, and $Gal(L/K)$ is cyclic, generated
by an element `σ`, then for every `x : L` such that $N_{L/K}(x) = 1,$ there exists `y : L` such
that $x = y/σ(y).$ Using the fact that `H¹(G, A) ≅ Ker(N_A)/(ρ(g) - 1)(A)` for any finite cyclic
group `G` with generator `g`, we deduce the original statement from Noether's generalization.

Noether's generalization also holds for infinite Galois extensions.

## Main statements

* `groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units`: Noether's generalization
  of Hilbert's Theorem 90: for all $f: Aut_K(L) \to L^\times$ satisfying the 1-cocycle
  condition, there exists `β : Lˣ` such that $g(β)/β = f(g)$ for all `g : Aut_K(L)`.
* `groupCohomology.H1ofAutOnUnitsUnique`: Noether's generalization of Hilbert's Theorem 90:
  $H^1(Aut_K(L), L^\times)$ is trivial.
* `groupCohomology.exists_div_of_norm_eq_one`: Hilbert's Theorem 90: given a finite cyclic Galois
  extension `L/K`, an element `x : L` such that `N_{L/K}(x) = 1`, and a generator `g` of
  `Gal(L/K)`, there exists `y : Lˣ` such that `y/g y = x`.

## Implementation notes

Given a commutative ring `k` and a group `G`, group cohomology is developed in terms of `k`-linear
`G`-representations on `k`-modules. Therefore stating Noether's generalization of Hilbert 90 in
terms of `H¹` requires us to turn the natural action of `Aut_K(L)` on `Lˣ` into a morphism
`Aut_K(L) →* (Additive Lˣ →ₗ[ℤ] Additive Lˣ)`. Thus we provide the non-`H¹` version too, as its
statement is clearer.

## TODO

* Develop Galois cohomology to extend Noether's result to infinite Galois extensions.
* "Additive Hilbert 90": let `L/K` be a finite Galois extension. Then $H^n(Gal(L/K), L)$ is trivial
  for all $1 ≤ n.$

-/

namespace groupCohomology

namespace Hilbert90

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

noncomputable def aux (f : Gal(L/K) → Lˣ) : L → L :=
  Finsupp.linearCombination L (fun φ : Gal(L/K) ↦ (φ : L → L))
    (Finsupp.equivFunOnFinite.symm (fun φ => (f φ : L)))

-- DISSOLVED: aux_ne_zero

  have : LinearIndependent L (fun (f : Gal(L/K)) => (f : L → L)) :=

    LinearIndependent.comp (ι' := Gal(L/K))

      (linearIndependent_monoidHom L L) (fun f => f)

      (fun x y h => by ext; exact DFunLike.ext_iff.1 h _)

  have h := linearIndependent_iff.1 this

    (Finsupp.equivFunOnFinite.symm (fun φ => (f φ : L)))

  fun H => Units.ne_zero (f 1) (DFunLike.ext_iff.1 (h H) 1)

end Hilbert90

open Hilbert90

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

theorem isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units
    (f : Gal(L/K) → Lˣ) (hf : IsMulCocycle₁ f) :
    IsMulCoboundary₁ f := by

  obtain ⟨z, hz⟩ : ∃ z, aux f z ≠ 0 :=

    not_forall.1 (fun H => aux_ne_zero f <| funext <| fun x => H x)

  have : aux f z = ∑ h, f h * h z := by simp [aux, Finsupp.linearCombination, Finsupp.sum_fintype]

  use (Units.mk0 (aux f z) hz)⁻¹

  intro g

  simp only [IsMulCocycle₁, AlgEquiv.smul_units_def,

    map_inv, div_inv_eq_mul, inv_mul_eq_iff_eq_mul, Units.ext_iff, this,

    Units.val_mul, Units.coe_map, Units.val_mk0, MonoidHom.coe_coe] at hf ⊢

  simp_rw [map_sum, map_mul, Finset.sum_mul, mul_assoc, mul_comm _ (f _ : L), ← mul_assoc, ← hf g]

  exact eq_comm.1 (Fintype.sum_bijective (fun i => g * i)

    (Group.mulLeft_bijective g) _ _ (fun i => rfl))

end

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

-- INSTANCE (free from Core): H1ofAutOnUnitsUnique

variable {K L} [IsGalois K L]

open Additive Rep

set_option backward.isDefEq.respectTransparency false in

theorem norm_ofAlgebraAutOnUnits_eq (x : Lˣ) :
    (toMul <| toAdditive ((Rep.ofAlgebraAutOnUnits K L).norm.hom
      (toAdditive.symm <| ofMul x))).1 = algebraMap K L (Algebra.norm K (x : L)) := by
  simp [Algebra.norm_eq_prod_automorphisms, Representation.norm]

variable [IsCyclic (L ≃ₐ[K] L)] {g : Gal(L/K)}

set_option backward.isDefEq.respectTransparency false in

attribute [local instance] IsCyclic.commGroup in

theorem exists_div_of_norm_eq_one (hg : ∀ x, x ∈ Subgroup.zpowers g) {x : L}
    (hx : Algebra.norm K x = 1) : ∃ y : Lˣ, y / g y = x := by
  classical
  suffices H : ∀ x, Algebra.norm K x = 1 → ∃ y : Lˣ, g y / y = x by
    have hxinv : Algebra.norm K x⁻¹ = 1 := by simp [Algebra.norm_inv, hx]
    obtain ⟨y, hy⟩ := H _ hxinv
    use y
    rw [IsUnit.div_eq_iff y.isUnit] at hy
    rw [hy]
    field_simp
  intro x hx
  let xu : Lˣ := (Algebra.norm_ne_zero_iff.1 <| hx ▸ zero_ne_one.symm).isUnit.unit
  have hx' : algebraMap K L (Algebra.norm K (xu : L)) = _ := congrArg (algebraMap K L) hx
  rw [← norm_ofAlgebraAutOnUnits_eq xu, map_one] at hx'
  have := FiniteCyclicGroup.groupCohomologyπOdd_eq_zero_iff (ofAlgebraAutOnUnits K L) g hg
    1 (by simp) ⟨toAdditive.symm <| ofMul xu, by simp_all⟩
  rcases this.1 (Subsingleton.elim (α := groupCohomology.H1 (Rep.ofAlgebraAutOnUnits K L)) _ _)
    with ⟨y, hy⟩
  use toMul <| toAdditive y
  have := Units.ext_iff.1 congr(toMul <| toAdditive $hy)
  simp only [ofAlgebraAutOnUnits.eq_1, sub_hom, hom_id,
    Representation.IntertwiningMap.sub_toLinearMap, Representation.IntertwiningMap.toLinearMap_id,
    LinearMap.sub_apply, Representation.IntertwiningMap.coe_toLinearMap, applyAsHom_apply,
    ofMulDistribMulAction_ρ_apply_apply, AlgEquiv.smul_units_def, LinearMap.id_coe, id_eq,
    toAdditive_symm_apply, toAdditive_apply, toMul_ofMul, IsUnit.unit_spec, xu] at this
  rw [← this, toMul_sub]
  simp

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Algebra A L] [Algebra A K]

variable [Algebra B L] [IsScalarTower A B L] [IsScalarTower A K L] [IsFractionRing A K] [IsDomain A]

variable [IsIntegralClosure B A L]

open scoped nonZeroDivisors

-- DISSOLVED: exists_mul_galRestrict_of_norm_eq_one

end groupCohomology
