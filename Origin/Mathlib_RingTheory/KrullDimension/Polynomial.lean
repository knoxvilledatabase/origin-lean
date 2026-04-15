/-
Extracted from RingTheory/KrullDimension/Polynomial.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Krull dimension of polynomial ring

This file proves properties of the Krull dimension of the polynomial ring over a commutative ring

## Main results

* `Polynomial.ringKrullDim_le`: the Krull dimension of the polynomial ring over a commutative ring
  `R` is less than `2 * (ringKrullDim R) + 1`.

For noetherian rings:
* `Polynomial.ringKrullDim_of_isNoetherianRing`: the Krull dimension of `R[X]` is `dim R + 1`.
* `MvPolynomial.ringKrullDim_of_isNoetherianRing`: the Krull dimension of `R[X₁, ..., Xₙ]` is
  `dim R + n`.
-/

theorem Polynomial.ringKrullDim_le {R : Type*} [CommRing R] :
    ringKrullDim (Polynomial R) ≤ 2 * (ringKrullDim R) + 1 := by
  rw [ringKrullDim, ringKrullDim]
  apply Order.krullDim_le_of_krullDim_preimage_le' (PrimeSpectrum.comap C) ?_ (fun p ↦ ?_)
  · exact fun {a b} h ↦ Ideal.comap_mono h
  · rw [show C = (algebraMap R (Polynomial R)) from rfl, Order.krullDim_eq_of_orderIso
      (PrimeSpectrum.preimageOrderIsoFiber R (Polynomial R) p), ← ringKrullDim,
      ← ringKrullDim_eq_of_ringEquiv (polyEquivTensor R (p.asIdeal.ResidueField)).toRingEquiv,
      ← Ring.krullDimLE_iff]
    infer_instance

variable {R : Type*} [CommRing R] [IsNoetherianRing R]

namespace Polynomial

open Ideal IsLocalization

private lemma height_eq_height_add_one_of_isMaximal (p : Ideal R) [p.IsMaximal] (P : Ideal R[X])
    [P.IsMaximal] [P.LiesOver p] : P.height = p.height + 1 := by
  let _ : Field (R ⧸ p) := Quotient.field p
  suffices h : (P.map (Ideal.Quotient.mk (Ideal.map (algebraMap R R[X]) p))).height = 1 by
    rw [height_eq_height_add_of_liesOver_of_hasGoingDown p, h]
  let e : (R[X] ⧸ (p.map (algebraMap R R[X]))) ≃+* (R ⧸ p)[X] :=
    (polynomialQuotientEquivQuotientPolynomial p).symm
  let P' : Ideal (R ⧸ p)[X] := Ideal.map e <| P.map (Ideal.Quotient.mk <| p.map (algebraMap R R[X]))
  have : (P.map (Ideal.Quotient.mk <| p.map (algebraMap R R[X]))).IsMaximal := by
    refine .map_of_surjective_of_ker_le Quotient.mk_surjective ?_
    rw [mk_ker, LiesOver.over (P := P) (p := p)]
    exact map_comap_le
  have : P'.IsMaximal := map_isMaximal_of_equiv e
  have : P'.height = 1 := IsPrincipalIdealRing.height_eq_one_of_isMaximal P' polynomial_not_isField
  rwa [← e.height_map <| P.map (Ideal.Quotient.mk <| p.map (algebraMap R R[X]))]

set_option backward.isDefEq.respectTransparency false in

lemma height_map_C (p : Ideal R) [p.IsMaximal] : (p.map C).height = p.height := by
  have : (p.map C).LiesOver p := ⟨IsMaximal.eq_of_le inferInstance IsPrime.ne_top' le_comap_map⟩
  simp [height_eq_height_add_of_liesOver_of_hasGoingDown p]

attribute [local instance] Polynomial.algebra Polynomial.isLocalization in

lemma height_eq_height_add_one (p : Ideal R)
    (P : Ideal R[X]) [P.IsMaximal] [P.LiesOver p] :
    P.height = p.height + 1 := by
  have : p.IsPrime := by rw [P.over_def p]; infer_instance
  let Rₚ := Localization.AtPrime p
  set p' : Ideal Rₚ := p.map (algebraMap R Rₚ) with p'_def
  have : p'.IsMaximal := by
    rw [p'_def, Localization.AtPrime.map_eq_maximalIdeal]
    exact IsLocalRing.maximalIdeal.isMaximal Rₚ
  let P' : Ideal Rₚ[X] := P.map (algebraMap R[X] Rₚ[X])
  have disj : Disjoint (p.primeCompl.map C : Set R[X]) P := by
    refine Set.disjoint_left.mpr fun a ⟨b, hb⟩ ha ↦ hb.1 ?_
    rwa [SetLike.mem_coe, LiesOver.over (P := P) (p := p), mem_comap, algebraMap_eq, hb.2]
  have eq := comap_map_of_isPrime_disjoint _ Rₚ[X] ‹P.IsMaximal›.isPrime disj
  have : (comap (algebraMap R[X] Rₚ[X]) P').IsMaximal := eq.symm ▸ ‹P.IsMaximal›
  have : P'.IsMaximal := .of_isLocalization_of_disjoint (p.primeCompl.map C)
  have : P'.LiesOver p' := liesOver_of_isPrime_of_disjoint p.primeCompl _ _ disj
  have eq1 : p.height = p'.height := by
    rw [height_map_of_disjoint p.primeCompl]
    exact Disjoint.symm <| Set.disjoint_left.mpr fun _ a b ↦ b a
  have eq2 : P.height = P'.height := by
    rw [height_map_of_disjoint (Submonoid.map C <| p.primeCompl) _ disj]
  rw [eq1, eq2]
  apply height_eq_height_add_one_of_isMaximal p' P'
