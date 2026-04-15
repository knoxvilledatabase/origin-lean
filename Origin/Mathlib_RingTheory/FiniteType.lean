/-
Extracted from RingTheory/FiniteType.lean
Genuine: 12 of 19 | Dissolved: 0 | Infrastructure: 7
-/
import Origin.Core

/-!
# Finiteness conditions in commutative algebra

In this file we define a notion of finiteness that is common in commutative algebra.

## Main declarations

- `Algebra.FiniteType`, `RingHom.FiniteType`, `AlgHom.FiniteType`
  all of these express that some object is finitely generated *as an algebra* over some base ring.

-/

open Function (Surjective)

open Polynomial

section ModuleAndAlgebra

universe uR uS uA uB uM uN

variable (R : Type uR) (S : Type uS) (A : Type uA) (B : Type uB) (M : Type uM) (N : Type uN)

class Algebra.FiniteType [CommSemiring R] [Semiring A] [Algebra R A] : Prop where
  out : (⊤ : Subalgebra R A).FG

namespace Module

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

namespace Finite

open Submodule Set

variable {R S M N}

section Algebra

-- INSTANCE (free from Core): (priority

end Algebra

end Finite

end Module

namespace Algebra

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra R A] [Algebra R B]

variable [AddCommMonoid M] [Module R M]

variable [AddCommMonoid N] [Module R N]

namespace FiniteType

theorem of_restrictScalars_finiteType [Algebra S A] [IsScalarTower R S A] [hA : FiniteType R A] :
    FiniteType S A := by
  obtain ⟨s, hS⟩ := hA.out
  refine ⟨⟨s, eq_top_iff.2 fun b => ?_⟩⟩
  have le : adjoin R (s : Set A) ≤ Subalgebra.restrictScalars R (adjoin S s) := by
    apply (Algebra.adjoin_le _ : adjoin R (s : Set A) ≤ Subalgebra.restrictScalars R (adjoin S ↑s))
    simp only [Subalgebra.coe_restrictScalars]
    exact Algebra.subset_adjoin
  exact le (eq_top_iff.1 hS b)

variable {R S A B}

theorem of_surjective [FiniteType R A] (f : A →ₐ[R] B) (hf : Surjective f) : FiniteType R B :=
  ⟨by
    convert ‹FiniteType R A›.1.map f
    simpa only [map_top f, @eq_comm _ ⊤, eq_top_iff, AlgHom.mem_range] using hf⟩

theorem equiv (hRA : FiniteType R A) (e : A ≃ₐ[R] B) : FiniteType R B :=
  hRA.of_surjective e e.surjective

theorem trans [Algebra S A] [IsScalarTower R S A] (hRS : FiniteType R S) (hSA : FiniteType S A) :
    FiniteType R A :=
  ⟨fg_trans' hRS.1 hSA.1⟩

-- INSTANCE (free from Core): quotient

-- INSTANCE (free from Core): [FiniteType

-- INSTANCE (free from Core): {ι

-- INSTANCE (free from Core): {ι

theorem iff_quotient_freeAlgebra :
    FiniteType R A ↔
      ∃ (s : Finset A) (f : FreeAlgebra R s →ₐ[R] A), Surjective f := by
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s, FreeAlgebra.lift _ (↑), ?_⟩
    rw [← Set.range_eq_univ, ← AlgHom.coe_range, ← adjoin_range_eq_range_freeAlgebra_lift,
      Subtype.range_coe_subtype, Finset.setOf_mem, hs, coe_top]
  · rintro ⟨s, f, hsur⟩
    exact .of_surjective f hsur

theorem iff_quotient_mvPolynomial :
    FiniteType R S ↔
      ∃ (s : Finset S) (f : MvPolynomial { x // x ∈ s } R →ₐ[R] S), Surjective f := by
  constructor
  · rintro ⟨s, hs⟩
    use s, MvPolynomial.aeval (↑)
    intro x
    rw [← Set.mem_range, ← AlgHom.coe_range, ← adjoin_eq_range, SetLike.mem_coe, hs]
    apply mem_top
  · rintro ⟨s, f, hsur⟩
    exact .of_surjective f hsur

theorem iff_quotient_freeAlgebra' : FiniteType R A ↔
    ∃ (ι : Type uA) (_ : Fintype ι) (f : FreeAlgebra R ι →ₐ[R] A), Surjective f := by
  constructor
  · rw [iff_quotient_freeAlgebra]
    rintro ⟨s, f, hsur⟩
    use { x : A // x ∈ s }, inferInstance, f
  · rintro ⟨ι, hfintype, f, hsur⟩
    letI : Fintype ι := hfintype
    exact .of_surjective f hsur

theorem iff_quotient_mvPolynomial' : FiniteType R S ↔
    ∃ (ι : Type uS) (_ : Fintype ι) (f : MvPolynomial ι R →ₐ[R] S), Surjective f := by
  constructor
  · rw [iff_quotient_mvPolynomial]
    rintro ⟨s, f, hsur⟩
    use { x : S // x ∈ s }, inferInstance, f
  · rintro ⟨ι, hfintype, f, hsur⟩
    letI : Fintype ι := hfintype
    exact .of_surjective f hsur

theorem iff_quotient_mvPolynomial'' :
    FiniteType R S ↔ ∃ (n : ℕ) (f : MvPolynomial (Fin n) R →ₐ[R] S), Surjective f := by
  constructor
  · rw [iff_quotient_mvPolynomial']
    rintro ⟨ι, hfintype, f, hsur⟩
    have equiv := MvPolynomial.renameEquiv R (Fintype.equivFin ι)
    exact ⟨Fintype.card ι, AlgHom.comp f equiv.symm.toAlgHom, by simpa using hsur⟩
  · rintro ⟨n, f, hsur⟩
    exact .of_surjective f hsur

-- INSTANCE (free from Core): prod

theorem _root_.Subalgebra.fg_iff_finiteType (S : Subalgebra R A) : S.FG ↔ Algebra.FiniteType R S :=
  S.fg_top.symm.trans ⟨fun h => ⟨h⟩, fun h => h.out⟩

lemma adjoin_of_finite {A : Type*} [CommSemiring A] [Algebra R A] {t : Set A} (h : Set.Finite t) :
    FiniteType R (Algebra.adjoin R t) := by
  rw [← Subalgebra.fg_iff_finiteType]
  exact ⟨h.toFinset, by simp⟩

end FiniteType

end Algebra

end ModuleAndAlgebra

namespace RingHom

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
