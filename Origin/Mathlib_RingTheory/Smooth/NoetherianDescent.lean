/-
Extracted from RingTheory/Smooth/NoetherianDescent.lean
Genuine: 7 of 15 | Dissolved: 0 | Infrastructure: 8
-/
import Origin.Core

/-!
# Smooth algebras have Noetherian models

In this file, we show if `S` is a smooth `R`-algebra, there exists a `ℤ`-subalgebra of finite type
`R₀` and a smooth `R₀`-algebra `S₀` such that `S ≃ₐ R ⊗[R₀] S₀`.

The analogous result for etale algebras is also provided.
-/

universe u

open TensorProduct MvPolynomial

namespace Algebra.Smooth

variable {R : Type*} [CommRing R]

variable {A : Type u} {B : Type*} [CommRing A] [Algebra R A] [CommRing B] [Algebra A B]

variable (A B) in

structure DescentAux where
  vars : Type
  rels : Type
  P : Presentation A B vars rels
  σ : B →ₐ[A] MvPolynomial vars A ⧸ P.ker ^ 2
  h : vars → MvPolynomial vars A
  p : rels → MvPolynomial rels (MvPolynomial vars A)
  hphom : ∀ (j : rels), (p j).IsHomogeneous 2
  hp : ∀ (j : rels), (eval P.relation) (p j) = (aeval h) (P.relation j)
  q : vars → MvPolynomial rels P.Ring
  hqhom : ∀ (i : vars), (q i).IsHomogeneous 1
  hq : ∀ (i : vars), (eval P.relation) (q i) = h i - X i

namespace DescentAux

variable (D : DescentAux A B)

variable (R)

def subalgebra (D : DescentAux A B) : Subalgebra R A :=
  Algebra.adjoin R
    (D.P.coeffs ∪
      ((⋃ i, (D.h i).coeffs) ∪
       (⋃ i, ⋃ x ∈ (D.q i).coeffs, x.coeffs) ∪
       (⋃ i, ⋃ x ∈ (D.p i).coeffs, x.coeffs)) : Set A)

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): algebra₀

-- INSTANCE (free from Core): algebra₁

-- INSTANCE (free from Core): algebra₂

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

lemma fg_subalgebra [Finite D.vars] [Finite D.rels] : (D.subalgebra R).FG := by
  refine Subalgebra.fg_def.mpr ⟨_, ?_, rfl⟩
  refine .union ?_ (.union (.union ?_ ?_) ?_)
  · exact Presentation.finite_coeffs
  · refine Set.finite_iUnion fun i ↦ Finset.finite_toSet _
  · refine Set.finite_iUnion fun i ↦ ?_
    exact Set.Finite.biUnion (Finset.finite_toSet _) (fun i hi ↦ Finset.finite_toSet _)
  · refine Set.finite_iUnion fun i ↦ ?_
    exact Set.Finite.biUnion (Finset.finite_toSet _) (fun i hi ↦ Finset.finite_toSet _)

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): hasCoeffs

set_option quotPrecheck false in

local notation "f₀" =>

  Ideal.Quotient.mkₐ (D.subalgebra R)

    (Ideal.span <| .range <| D.P.relationOfHasCoeffs (D.subalgebra R))

set_option backward.isDefEq.respectTransparency false in

lemma coeffs_h_subset (i) : ↑(D.h i).coeffs ⊆ Set.range ⇑(algebraMap (D.subalgebra R) A) := by
  have : ((D.h i).coeffs : Set _) ⊆ ⋃ i, ((D.h i).coeffs : Set A) :=
    Set.subset_iUnion_of_subset i subset_rfl
  #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
  (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal
  without the `rw`. It is not yet clear whether this is due to defeq abuse in Mathlib or a
  problem in the new canonicalizer; a minimization would help. The original proof was:
  `grind [subalgebra, Subalgebra.setRange_algebraMap, Algebra.subset_adjoin]` -/
  rw [Subalgebra.setRange_algebraMap]
  grind [subalgebra, Algebra.subset_adjoin]

set_option backward.isDefEq.respectTransparency false in

lemma coeffs_p_subset (i) :
    ↑(D.p i).coeffs ⊆
      Set.range (MvPolynomial.map (σ := D.vars) (algebraMap (D.subalgebra R) A)) := by
  intro p hp
  have : (p.coeffs : Set A) ⊆ ⋃ i, ⋃ x ∈ (D.p i).coeffs, ↑x.coeffs :=
    Set.subset_iUnion_of_subset i (Set.subset_iUnion₂_of_subset p hp subset_rfl)
  #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
  (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal
  without the `rw`. It is not yet clear whether this is due to defeq abuse in Mathlib or a
  problem in the new canonicalizer; a minimization would help. The original proof was:
  `grind [MvPolynomial.mem_range_map_iff_coeffs_subset, subalgebra,
    Subalgebra.setRange_algebraMap, Algebra.subset_adjoin]` -/
  rw [MvPolynomial.mem_range_map_iff_coeffs_subset, Subalgebra.setRange_algebraMap]
  grind [subalgebra, Algebra.subset_adjoin]

set_option backward.isDefEq.respectTransparency false in

lemma coeffs_q_subset (i) :
    ↑(D.q i).coeffs ⊆
      Set.range (MvPolynomial.map (σ := D.vars) (algebraMap (D.subalgebra R) A)) := by
  intro q hq
  have : (q.coeffs : Set A) ⊆ ⋃ i, ⋃ x ∈ (D.q i).coeffs, ↑(coeffs x) :=
    Set.subset_iUnion_of_subset i (Set.subset_iUnion₂_of_subset q hq subset_rfl)
  #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
  (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal
  without the `rw`. It is not yet clear whether this is due to defeq abuse in Mathlib or a
  problem in the new canonicalizer; a minimization would help. The original proof was:
  `grind [MvPolynomial.mem_range_map_iff_coeffs_subset, subalgebra,
    Subalgebra.setRange_algebraMap, Algebra.subset_adjoin]` -/
  rw [MvPolynomial.mem_range_map_iff_coeffs_subset, Subalgebra.setRange_algebraMap]
  grind [subalgebra, Algebra.subset_adjoin]

set_option backward.isDefEq.respectTransparency false in

lemma exists_kerSquareLift_comp_eq_id :
    ∃ (σ₀ : D.P.ModelOfHasCoeffs (D.subalgebra R) →ₐ[D.subalgebra R]
        MvPolynomial D.vars (D.subalgebra R) ⧸ (RingHom.ker f₀ ^ 2)),
      (AlgHom.kerSquareLift f₀).comp σ₀ =
        .id (D.subalgebra R) (Presentation.ModelOfHasCoeffs (D.subalgebra R)) := by
  choose p hp using fun i ↦ (D.h i).mem_range_map_iff_coeffs_subset.mpr (D.coeffs_h_subset R i)
  refine ⟨?_, ?_⟩
  · refine Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ _ _).comp <| aeval p) ?_
    simp_rw [← RingHom.mem_ker, ← SetLike.le_def, Ideal.span_le, Set.range_subset_iff]
    intro i
    simp only [← AlgHom.comap_ker, Ideal.coe_comap, Set.mem_preimage, SetLike.mem_coe]
    rw [← RingHom.ker_coe_toRingHom, Ideal.Quotient.mkₐ_ker,
      ← RingHom.ker_coe_toRingHom, Ideal.Quotient.mkₐ_ker]
    have hinj : Function.Injective
        (MvPolynomial.map (σ := D.vars) (algebraMap (D.subalgebra R) A)) :=
      map_injective _ (FaithfulSMul.algebraMap_injective (D.subalgebra R) A)
    rw [Ideal.mem_span_pow_iff_exists_isHomogeneous]
    obtain ⟨q, hq⟩ := (D.p i).mem_range_map_iff_coeffs_subset.mpr (D.coeffs_p_subset R i)
    refine ⟨q, .of_map hinj ?_, hinj ?_⟩
    · rw [hq]
      exact D.hphom i
    · simp_rw [map_eval, Function.comp_def, Presentation.map_relationOfHasCoeffs,
        hq, D.hp, MvPolynomial.map_aeval, hp]
      simp [MvPolynomial.eval₂_map_comp_C, Presentation.map_relationOfHasCoeffs, aeval_def]
  · have hf₀ : Function.Surjective f₀ := Ideal.Quotient.mk_surjective
    rw [← AlgHom.cancel_right hf₀]
    refine MvPolynomial.algHom_ext fun i ↦ ?_
    suffices h : ∃ p', p'.IsHomogeneous 1 ∧ (eval (D.P.relationOfHasCoeffs (D.subalgebra R))) p' =
        p i - X i by
      -- Reducible def-eq issues caused by `RingHom.ker f.toRingHom` discrepancies
      -- Can be fixed after #25138.
      apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
      simpa [Ideal.mem_span_iff_exists_isHomogeneous, hp]
    have hinj : Function.Injective
        (MvPolynomial.map (σ := D.vars) (algebraMap (D.subalgebra R) A)) :=
      map_injective _ (FaithfulSMul.algebraMap_injective (D.subalgebra R) A)
    obtain ⟨t, ht⟩ := (D.q i).mem_range_map_iff_coeffs_subset.mpr (D.coeffs_q_subset R i)
    refine ⟨t, .of_map hinj ?_, hinj ?_⟩
    · rw [ht]
      exact D.hqhom i
    · simp [MvPolynomial.map_eval, Function.comp_def,
        Presentation.map_relationOfHasCoeffs, ht, hq, hp]

end DescentAux

variable (R A B)

set_option backward.isDefEq.respectTransparency false in
