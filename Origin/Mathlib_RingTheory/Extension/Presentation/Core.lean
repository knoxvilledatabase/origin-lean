/-
Extracted from RingTheory/Extension/Presentation/Core.lean
Genuine: 14 of 22 | Dissolved: 0 | Infrastructure: 8
-/
import Origin.Core

/-!
# Presentations on subrings

In this file we establish the API for realising a presentation over a
subring of `R`. We define a property `HasCoeffs R₀` for a presentation `P` to mean
the (sub)ring `R₀` contains the coefficients of the relations of `P`.
subring `R₀` of `R` that contains the coefficients of the relations
In this case there exists a model of `S` over `R₀`, i.e., there exists an `R₀`-algebra `S₀`
such that `S` is isomorphic to `R ⊗[R₀] S₀`.

If the presentation is finite, `R₀` may be chosen as a Noetherian ring. In this case,
this API can be used to remove Noetherian hypothesis in certain cases.

-/

open TensorProduct

variable {R S ι σ : Type*} [CommRing R] [CommRing S] [Algebra R S]

variable {P : Algebra.Presentation R S ι σ}

namespace Algebra.Presentation

variable (P) in

def coeffs : Set R := ⋃ (i : σ), (P.relation i).coeffs

lemma coeffs_relation_subset_coeffs (x : σ) :
    ((P.relation x).coeffs : Set R) ⊆ P.coeffs :=
  Set.subset_iUnion_of_subset x (by simp)

lemma finite_coeffs [Finite σ] : P.coeffs.Finite :=
  Set.finite_iUnion fun _ ↦ Finset.finite_toSet _

variable (P) in

def core : Subalgebra ℤ R := Algebra.adjoin _ P.coeffs

variable (P) in

lemma coeffs_subset_core : P.coeffs ⊆ P.core := Algebra.subset_adjoin

lemma coeffs_relation_subset_core (x : σ) :
    ((P.relation x).coeffs : Set R) ⊆ P.core :=
  subset_trans (P.coeffs_relation_subset_coeffs x) P.coeffs_subset_core

variable (P) in

def Core : Type _ := P.core

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): [Finite

variable (P) in

class HasCoeffs (R₀ : Type*) [CommRing R₀] [Algebra R₀ R] [Algebra R₀ S]
    [IsScalarTower R₀ R S] where
  coeffs_subset_range : P.coeffs ⊆ Set.range (algebraMap R₀ R)

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): :

variable (R₀ : Type*) [CommRing R₀] [Algebra R₀ R] [Algebra R₀ S] [IsScalarTower R₀ R S]
  [P.HasCoeffs R₀]

lemma coeffs_subset_range : (P.coeffs : Set R) ⊆ Set.range (algebraMap R₀ R) :=
  HasCoeffs.coeffs_subset_range

lemma HasCoeffs.of_isScalarTower {R₁ : Type*} [CommRing R₁] [Algebra R₀ R₁] [Algebra R₁ R]
    [IsScalarTower R₀ R₁ R] [Algebra R₁ S] [IsScalarTower R₁ R S] :
    P.HasCoeffs R₁ := by
  refine ⟨subset_trans (P.coeffs_subset_range R₀) ?_⟩
  simp [IsScalarTower.algebraMap_eq R₀ R₁ R, RingHom.coe_comp, Set.range_comp]

-- INSTANCE (free from Core): (s

lemma HasCoeffs.coeffs_relation_mem_range (x : σ) :
    ↑(P.relation x).coeffs ⊆ Set.range (algebraMap R₀ R) :=
  subset_trans (P.coeffs_relation_subset_coeffs x) HasCoeffs.coeffs_subset_range

lemma HasCoeffs.relation_mem_range_map (x : σ) :
    P.relation x ∈ Set.range (MvPolynomial.map (algebraMap R₀ R)) := by
  rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
  exact HasCoeffs.coeffs_relation_mem_range R₀ x

noncomputable def relationOfHasCoeffs (r : σ) : MvPolynomial ι R₀ :=
  (HasCoeffs.relation_mem_range_map (P := P) R₀ r).choose

lemma map_relationOfHasCoeffs (r : σ) :
    MvPolynomial.map (algebraMap R₀ R) (P.relationOfHasCoeffs R₀ r) = P.relation r :=
  (HasCoeffs.relation_mem_range_map R₀ r).choose_spec
