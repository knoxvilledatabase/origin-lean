/-
Extracted from RingTheory/Kaehler/Polynomial.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The Kähler differential module of polynomial algebras
-/

open Algebra Module

open scoped TensorProduct

universe u v

variable (R : Type u) [CommRing R]

suppress_compilation

section MvPolynomial

def KaehlerDifferential.mvPolynomialEquiv (σ : Type*) :
    Ω[MvPolynomial σ R⁄R] ≃ₗ[MvPolynomial σ R] σ →₀ MvPolynomial σ R where
  __ := (MvPolynomial.mkDerivation _ (Finsupp.single · 1)).liftKaehlerDifferential
  invFun := Finsupp.linearCombination (α := σ) _ (fun x ↦ D _ _ (MvPolynomial.X x))
  right_inv := by
    intro x
    induction x using Finsupp.induction_linear with
    | zero => simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]; rw [map_zero, map_zero]
    | add => simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, map_add] at *; simp only [*]
    | single a b => simp [-map_smul]
  left_inv := by
    intro x
    obtain ⟨x, rfl⟩ := linearCombination_surjective _ _ x
    induction x using Finsupp.induction_linear with
    | zero =>
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]
      rw [map_zero, map_zero, map_zero]
    | add => simp only [map_add, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom] at *; simp only [*]
    | single a b =>
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, Finsupp.linearCombination_single,
        map_smul, Derivation.liftKaehlerDifferential_comp_D]
      congr 1
      induction a using MvPolynomial.induction_on
      · simp only [MvPolynomial.derivation_C, map_zero]
      · simp only [map_add, *]
      · simp [*]

def KaehlerDifferential.mvPolynomialBasis (σ) :
    Basis σ (MvPolynomial σ R) Ω[MvPolynomial σ R⁄R] :=
  ⟨mvPolynomialEquiv R σ⟩

lemma KaehlerDifferential.mvPolynomialBasis_repr_comp_D (σ) :
    (mvPolynomialBasis R σ).repr.toLinearMap.compDer (D _ _) =
      MvPolynomial.mkDerivation _ (Finsupp.single · 1) :=
  Derivation.liftKaehlerDifferential_comp _

lemma KaehlerDifferential.mvPolynomialBasis_repr_D (σ) (x) :
    (mvPolynomialBasis R σ).repr (D _ _ x) =
      MvPolynomial.mkDerivation R (Finsupp.single · (1 : MvPolynomial σ R)) x :=
  Derivation.congr_fun (mvPolynomialBasis_repr_comp_D R σ) x
