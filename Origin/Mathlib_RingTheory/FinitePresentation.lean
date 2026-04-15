/-
Extracted from RingTheory/FinitePresentation.lean
Genuine: 9 of 14 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-!
# Finiteness conditions in commutative algebra

In this file we define several notions of finiteness that are common in commutative algebra.

## Main declarations

- `Module.Finite`, `RingHom.Finite`, `AlgHom.Finite`
  all of these express that some object is finitely generated *as module* over some base ring.
- `Algebra.FiniteType`, `RingHom.FiniteType`, `AlgHom.FiniteType`
  all of these express that some object is finitely generated *as algebra* over some base ring.
- `Algebra.FinitePresentation`, `RingHom.FinitePresentation`, `AlgHom.FinitePresentation`
  all of these express that some object is finitely presented *as algebra* over some base ring.

-/

open Function (Surjective)

open Polynomial

section ModuleAndAlgebra

universe w₁ w₂ w₃

variable (R : Type w₁) (A : Type w₂) (B : Type w₃)

class Algebra.FinitePresentation [CommSemiring R] [Semiring A] [Algebra R A] : Prop where
  out : ∃ (n : ℕ) (f : MvPolynomial (Fin n) R →ₐ[R] A), Surjective f ∧ (RingHom.ker f.toRingHom).FG

namespace Algebra

variable [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

namespace FiniteType

variable {R A B}

-- INSTANCE (free from Core): of_finitePresentation

end FiniteType

namespace FinitePresentation

variable {R A B}

theorem of_finiteType [IsNoetherianRing R] : FiniteType R A ↔ FinitePresentation R A := by
  refine ⟨fun h => ?_, fun hfp => Algebra.FiniteType.of_finitePresentation⟩
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 h
  refine ⟨n, f, hf, ?_⟩
  exact (inferInstance : IsNoetherianRing (MvPolynomial (Fin n) R)).noetherian
    (RingHom.ker f.toRingHom)

variable (R)

private lemma mvPolynomial_aux (ι : Type*) [Finite ι] :
    FinitePresentation R (MvPolynomial ι R) where
  out := by
    cases nonempty_fintype ι
    let eqv := (MvPolynomial.renameEquiv R <| Fintype.equivFin ι).symm
    exact
      ⟨Fintype.card ι, eqv, eqv.surjective,
        ((RingHom.injective_iff_ker_eq_bot _).1 eqv.injective).symm ▸ Submodule.fg_bot⟩

variable {R}

protected theorem quotient {I : Ideal A} (h : I.FG) [FinitePresentation R A] :
    FinitePresentation R (A ⧸ I) where
  out := by
    obtain ⟨n, f, hf⟩ := FinitePresentation.out (R := R) (A := A)
    refine ⟨n, (Ideal.Quotient.mkₐ R I).comp f, ?_, ?_⟩
    · exact (Ideal.Quotient.mkₐ_surjective R I).comp hf.1
    · refine Ideal.fg_ker_comp _ _ hf.2 ?_ hf.1
      simp [h]

theorem of_surjective {f : A →ₐ[R] B} (hf : Function.Surjective f)
    (hker : (RingHom.ker f.toRingHom).FG)
    [FinitePresentation R A] : FinitePresentation R B :=
  letI : FinitePresentation R (A ⧸ RingHom.ker f) := FinitePresentation.quotient hker
  equiv (Ideal.quotientKerAlgEquivOfSurjective hf)

theorem iff :
    FinitePresentation R A ↔
      ∃ (n : _) (I : Ideal (MvPolynomial (Fin n) R)) (_ : (_ ⧸ I) ≃ₐ[R] A), I.FG := by
  constructor
  · rintro ⟨n, f, hf⟩
    exact ⟨n, RingHom.ker f.toRingHom, Ideal.quotientKerAlgEquivOfSurjective hf.1, hf.2⟩
  · rintro ⟨n, I, e, hfg⟩
    letI := (FinitePresentation.mvPolynomial_aux R _).quotient hfg
    exact equiv e

theorem iff_quotient_mvPolynomial' :
    FinitePresentation R A ↔
      ∃ (ι : Type*) (_ : Fintype ι) (f : MvPolynomial ι R →ₐ[R] A),
        Surjective f ∧ (RingHom.ker f.toRingHom).FG := by
  constructor
  · rintro ⟨n, f, hfs, hfk⟩
    set ulift_var := MvPolynomial.renameEquiv R Equiv.ulift
    refine
      ⟨ULift (Fin n), inferInstance, f.comp ulift_var.toAlgHom, hfs.comp ulift_var.surjective,
        Ideal.fg_ker_comp _ _ ?_ hfk ulift_var.surjective⟩
    simpa using Submodule.fg_bot
  · rintro ⟨ι, hfintype, f, hf⟩
    have equiv := MvPolynomial.renameEquiv R (Fintype.equivFin ι)
    use Fintype.card ι, f.comp equiv.symm, hf.1.comp (AlgEquiv.symm equiv).surjective
    refine Ideal.fg_ker_comp (S := MvPolynomial ι R) (A := A) _ f ?_ hf.2 equiv.symm.surjective
    simpa using Submodule.fg_bot

universe v in

theorem mvPolynomial_of_finitePresentation [FinitePresentation R A] (ι : Type v) [Finite ι] :
    FinitePresentation R (MvPolynomial ι A) := by
  have hfp : FinitePresentation R A := inferInstance
  rw [iff_quotient_mvPolynomial'] at hfp ⊢
  classical
  -- Make universe level `v` explicit so it matches that of `ι`
  obtain ⟨(ι' : Type v), _, f, hf_surj, hf_ker⟩ := hfp
  let g := (MvPolynomial.mapAlgHom f).comp (MvPolynomial.sumAlgEquiv R ι ι').toAlgHom
  cases nonempty_fintype (ι ⊕ ι')
  refine
    ⟨ι ⊕ ι', by infer_instance, g,
      (MvPolynomial.map_surjective f.toRingHom hf_surj).comp (AlgEquiv.surjective _),
      Ideal.fg_ker_comp _ _ ?_ ?_ (AlgEquiv.surjective _)⟩
  · rw [AlgEquiv.toAlgHom_eq_coe, AlgEquiv.toAlgHom_toRingHom, AlgHom.ker_coe_equiv]
    exact Submodule.fg_bot
  · rw [AlgHom.toRingHom_eq_coe, MvPolynomial.mapAlgHom_coe_ringHom, MvPolynomial.ker_map]
    exact hf_ker.map MvPolynomial.C

variable (R A B)

theorem trans [Algebra A B] [IsScalarTower R A B] [FinitePresentation R A]
    [FinitePresentation A B] : FinitePresentation R B := by
  have hfpB : FinitePresentation A B := inferInstance
  obtain ⟨n, I, e, hfg⟩ := iff.1 hfpB
  letI : FinitePresentation R (MvPolynomial (Fin n) A ⧸ I) :=
    (mvPolynomial_of_finitePresentation _).quotient hfg
  exact equiv (e.restrictScalars R)

-- INSTANCE (free from Core): mvPolynomial

-- INSTANCE (free from Core): self

-- INSTANCE (free from Core): polynomial

open MvPolynomial
