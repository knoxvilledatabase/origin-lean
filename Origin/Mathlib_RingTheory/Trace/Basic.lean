/-
Extracted from RingTheory/Trace/Basic.lean
Genuine: 18 of 19 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Trace for (finite) ring extensions.

Suppose we have an `R`-algebra `S` with a finite basis. For each `s : S`,
the trace of the linear map given by multiplying by `s` gives information about
the roots of the minimal polynomial of `s` over `R`.

## Main definitions

* `Algebra.embeddingsMatrix A C b : Matrix κ (B →ₐ[A] C) C` is the matrix whose
  `(i, σ)` coefficient is `σ (b i)`.
* `Algebra.embeddingsMatrixReindex A C b e : Matrix κ κ C` is the matrix whose `(i, j)`
  coefficient is `σⱼ (b i)`, where `σⱼ : B →ₐ[A] C` is the embedding corresponding to `j : κ`
  given by a bijection `e : κ ≃ (B →ₐ[A] C)`.
* `Module.Basis.traceDual`: The dual basis of a basis under the trace form in a finite separable
  extension.

## Main results

* `trace_eq_sum_embeddings`: the trace of `x : K(x)` is the sum of all embeddings of `x` into an
  algebraically closed field
* `traceForm_nondegenerate`: the trace form over a separable extension is a nondegenerate
  bilinear form
* `Module.Basis.traceDual_powerBasis_eq`: The dual basis of a power basis `{1, x, x²...}` under the
  trace form is `aᵢ / f'(x)`, with `f` being the minpoly of `x` and `f / (X - x) = ∑ aᵢxⁱ`.

## References

* https://en.wikipedia.org/wiki/Field_trace

-/

universe u v w z

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

variable [Algebra R S] [Algebra R T]

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

variable {ι κ : Type w}

open Module

open LinearMap (BilinForm)

open LinearMap

open Matrix

open scoped Matrix

theorem Algebra.traceForm_toMatrix_powerBasis (h : PowerBasis R S) :
    (traceForm R S).toMatrix h.basis = of fun i j => trace R S (h.gen ^ (i.1 + j.1)) := by
  ext; rw [traceForm_toMatrix, of_apply, pow_add, h.basis_eq_pow, h.basis_eq_pow]

section EqSumRoots

open Algebra Polynomial

variable {F : Type*} [Field F]

variable [Algebra K S] [Algebra K F]

theorem PowerBasis.trace_gen_eq_nextCoeff_minpoly [Nontrivial S] (pb : PowerBasis K S) :
    Algebra.trace K S pb.gen = -(minpoly K pb.gen).nextCoeff := by
  have d_pos : 0 < pb.dim := PowerBasis.dim_pos pb
  have d_pos' : 0 < (minpoly K pb.gen).natDegree := by simpa
  haveI : Nonempty (Fin pb.dim) := ⟨⟨0, d_pos⟩⟩
  rw [trace_eq_matrix_trace pb.basis, trace_eq_neg_charpoly_coeff, charpoly_leftMulMatrix, ←
    pb.natDegree_minpoly, Fintype.card_fin, ← nextCoeff_of_natDegree_pos d_pos']

theorem PowerBasis.trace_gen_eq_sum_roots [Nontrivial S] (pb : PowerBasis K S)
    (hf : ((minpoly K pb.gen).map (algebraMap K F)).Splits) :
    algebraMap K F (trace K S pb.gen) = ((minpoly K pb.gen).aroots F).sum := by
  rw [PowerBasis.trace_gen_eq_nextCoeff_minpoly, map_neg,
    ← nextCoeff_map_eq, hf.nextCoeff_eq_neg_sum_roots_of_monic
      ((minpoly.monic (PowerBasis.isIntegral_gen _)).map _),
    neg_neg]

namespace IntermediateField.AdjoinSimple

open IntermediateField

theorem trace_gen_eq_zero {x : L} (hx : ¬IsIntegral K x) :
    Algebra.trace K K⟮x⟯ (AdjoinSimple.gen K x) = 0 := by
  rw [trace_eq_zero_of_not_exists_basis, LinearMap.zero_apply]
  contrapose hx
  obtain ⟨s, ⟨b⟩⟩ := hx
  refine .of_mem_of_fg K⟮x⟯.toSubalgebra ?_ x ?_
  · exact (Submodule.fg_iff_finiteDimensional _).mpr (b.finiteDimensional_of_finite)
  · exact subset_adjoin K _ (Set.mem_singleton x)

theorem trace_gen_eq_sum_roots (x : L) (hf : ((minpoly K x).map (algebraMap K F)).Splits) :
    algebraMap K F (trace K K⟮x⟯ (AdjoinSimple.gen K x)) =
      ((minpoly K x).aroots F).sum := by
  have injKxL := (algebraMap K⟮x⟯ L).injective
  by_cases hx : IsIntegral K x; swap
  · simp [minpoly.eq_zero hx, trace_gen_eq_zero hx, aroots_def]
  rw [← adjoin.powerBasis_gen hx, (adjoin.powerBasis hx).trace_gen_eq_sum_roots] <;>
    rw [adjoin.powerBasis_gen hx, ← minpoly.algebraMap_eq injKxL] <;>
    try simp only [AdjoinSimple.algebraMap_gen _ _]
  exact hf

end IntermediateField.AdjoinSimple

open IntermediateField

variable (K)

theorem trace_eq_trace_adjoin [FiniteDimensional K L] (x : L) :
    trace K L x = finrank K⟮x⟯ L • trace K K⟮x⟯ (AdjoinSimple.gen K x) := by
  rw [← trace_trace (S := K⟮x⟯)]
  conv in x => rw [← AdjoinSimple.algebraMap_gen K x]
  rw [trace_algebraMap, LinearMap.map_smul_of_tower]

variable {K} in

theorem trace_adjoinSimpleGen {x : L} (hx : IsIntegral K x) :
    trace K K⟮x⟯ (AdjoinSimple.gen K x) = -(minpoly K x).nextCoeff := by
  simpa [minpoly_gen K x] using PowerBasis.trace_gen_eq_nextCoeff_minpoly <| adjoin.powerBasis hx

theorem trace_eq_finrank_mul_minpoly_nextCoeff [FiniteDimensional K L] (x : L) :
    trace K L x = finrank K⟮x⟯ L * -(minpoly K x).nextCoeff := by
  rw [trace_eq_trace_adjoin, trace_adjoinSimpleGen (.of_finite K x), Algebra.smul_def]; rfl

variable {K}

theorem trace_eq_sum_roots [FiniteDimensional K L] {x : L}
    (hF : ((minpoly K x).map (algebraMap K F)).Splits) :
    algebraMap K F (Algebra.trace K L x) =
      finrank K⟮x⟯ L • ((minpoly K x).aroots F).sum := by
  rw [trace_eq_trace_adjoin K x, Algebra.smul_def, map_mul, ← Algebra.smul_def,
    IntermediateField.AdjoinSimple.trace_gen_eq_sum_roots _ hF, IsScalarTower.algebraMap_smul]

end EqSumRoots

variable {F : Type*} [Field F]

variable [Algebra R L] [Algebra L F] [Algebra R F] [IsScalarTower R L F]

open Polynomial

attribute [-instance] Field.toEuclideanDomain

theorem Algebra.isIntegral_trace [FiniteDimensional L F] {x : F} (hx : IsIntegral R x) :
    IsIntegral R (Algebra.trace L F x) := by
  have hx' : IsIntegral L x := hx.tower_top
  rw [← isIntegral_algebraMap_iff (algebraMap L (AlgebraicClosure F)).injective, trace_eq_sum_roots]
  · refine (IsIntegral.multiset_sum ?_).nsmul _
    intro y hy
    rw [mem_roots_map (minpoly.ne_zero hx')] at hy
    use minpoly R x, minpoly.monic hx
    rw [← aeval_def] at hy ⊢
    exact minpoly.aeval_of_isScalarTower R x y hy
  · apply IsAlgClosed.splits

lemma Algebra.trace_eq_of_algEquiv {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] (e : B ≃ₐ[A] C) (x) :
    Algebra.trace A C (e x) = Algebra.trace A B x := by
  simp_rw [Algebra.trace_apply, ← LinearMap.trace_conj' _ e.toLinearEquiv]
  congr; ext; simp

set_option backward.isDefEq.respectTransparency false in

lemma Algebra.trace_eq_of_equiv_equiv {A₁ B₁ A₂ B₂ : Type*} [CommRing A₁] [CommRing B₁]
    [CommRing A₂] [CommRing B₂] [Algebra A₁ B₁] [Algebra A₂ B₂] (e₁ : A₁ ≃+* A₂) (e₂ : B₁ ≃+* B₂)
    (he : RingHom.comp (algebraMap A₂ B₂) ↑e₁ = RingHom.comp ↑e₂ (algebraMap A₁ B₁)) (x) :
    Algebra.trace A₁ B₁ x = e₁.symm (Algebra.trace A₂ B₂ (e₂ x)) := by
  letI := (RingHom.comp (e₂ : B₁ →+* B₂) (algebraMap A₁ B₁)).toAlgebra
  let e' : B₁ ≃ₐ[A₁] B₂ := { e₂ with commutes' := fun _ ↦ rfl }
  rw [← Algebra.trace_eq_of_ringEquiv e₁ he, ← Algebra.trace_eq_of_algEquiv e',
    RingEquiv.symm_apply_apply]
  rfl

section EqSumEmbeddings

variable [Algebra K F] [IsScalarTower K L F]

open Algebra IntermediateField

variable (F) (E : Type*) [Field E] [Algebra K E]

theorem trace_eq_sum_embeddings_gen (pb : PowerBasis K L)
    (hE : ((minpoly K pb.gen).map (algebraMap K E)).Splits) (hfx : IsSeparable K pb.gen) :
    algebraMap K E (Algebra.trace K L pb.gen) =
      (@Finset.univ _ (PowerBasis.AlgHom.fintype pb)).sum fun σ => σ pb.gen := by
  letI := Classical.decEq E
  letI : Fintype (L →ₐ[K] E) := PowerBasis.AlgHom.fintype pb
  rw [pb.trace_gen_eq_sum_roots hE, Fintype.sum_equiv pb.liftEquiv', Finset.sum_mem_multiset,
    Finset.sum_eq_multiset_sum, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr _,
    Multiset.map_id]
  · exact nodup_roots ((separable_map _).mpr hfx)
  swap
  · intro x; rfl
  · intro σ
    rw [PowerBasis.liftEquiv'_apply_coe, id_def]

variable [IsAlgClosed E]

theorem sum_embeddings_eq_finrank_mul [FiniteDimensional K F] [Algebra.IsSeparable K F]
    (pb : PowerBasis K L) :
    ∑ σ : F →ₐ[K] E, σ (algebraMap L F pb.gen) =
      finrank L F •
        (@Finset.univ _ (PowerBasis.AlgHom.fintype pb)).sum fun σ : L →ₐ[K] E => σ pb.gen := by
  haveI : FiniteDimensional L F := FiniteDimensional.right K L F
  haveI : Algebra.IsSeparable L F := Algebra.isSeparable_tower_top_of_isSeparable K L F
  letI : Fintype (L →ₐ[K] E) := PowerBasis.AlgHom.fintype pb
  rw [Fintype.sum_equiv algHomEquivSigma (fun σ : F →ₐ[K] E => _) fun σ => σ.1 pb.gen,
    ← Finset.univ_sigma_univ, Finset.sum_sigma, ← Finset.sum_nsmul]
  · refine Finset.sum_congr rfl fun σ _ => ?_
    letI : Algebra L E := σ.toRingHom.toAlgebra
    simp_rw [Finset.sum_const, Finset.card_univ, ← AlgHom.card L F E]
  · intro σ
    simp only [algHomEquivSigma, Equiv.coe_fn_mk, AlgHom.restrictDomain, AlgHom.comp_apply,
      IsScalarTower.coe_toAlgHom']

theorem trace_eq_sum_embeddings [FiniteDimensional K L] [Algebra.IsSeparable K L] {x : L} :
    algebraMap K E (Algebra.trace K L x) = ∑ σ : L →ₐ[K] E, σ x := by
  have hx := Algebra.IsSeparable.isIntegral K x
  let pb := adjoin.powerBasis hx
  rw [trace_eq_trace_adjoin K x, Algebra.smul_def, map_mul, ← adjoin.powerBasis_gen hx,
    trace_eq_sum_embeddings_gen E pb (IsAlgClosed.splits _), ← Algebra.smul_def,
    algebraMap_smul]
  · exact (sum_embeddings_eq_finrank_mul L E pb).symm
  · haveI := Algebra.isSeparable_tower_bot_of_isSeparable K K⟮x⟯ L
    exact Algebra.IsSeparable.isSeparable K _

theorem trace_eq_sum_automorphisms (x : L) [FiniteDimensional K L] [IsGalois K L] :
    algebraMap K L (Algebra.trace K L x) = ∑ σ : Gal(L/K), σ x := by
  apply FaithfulSMul.algebraMap_injective L (AlgebraicClosure L)
  rw [_root_.map_sum (algebraMap L (AlgebraicClosure L))]
  rw [← Fintype.sum_equiv (Normal.algHomEquivAut K (AlgebraicClosure L) L)]
  · rw [← trace_eq_sum_embeddings (AlgebraicClosure L) (x := x)]
    simp only [algebraMap_eq_smul_one, smul_one_smul]
  · intro σ
    simp only [Normal.algHomEquivAut, AlgHom.restrictNormal', Equiv.coe_fn_mk,
      AlgEquiv.coe_ofBijective, AlgHom.restrictNormal_commutes, algebraMap_self, RingHom.id_apply]

end EqSumEmbeddings

section NotIsSeparable

lemma Algebra.trace_eq_zero_of_not_isSeparable (H : ¬ Algebra.IsSeparable K L) :
    trace K L = 0 := by
  obtain ⟨p, hp⟩ := ExpChar.exists K
  have := expChar_ne_zero K p
  ext x
  by_cases h₀ : FiniteDimensional K L; swap
  · rw [trace_eq_zero_of_not_exists_basis]
    rintro ⟨s, ⟨b⟩⟩
    exact h₀ (Module.Finite.of_basis b)
  by_cases hx : IsSeparable K x
  · lift x to separableClosure K L using hx
    rw [← IntermediateField.algebraMap_apply, ← trace_trace (S := separableClosure K L),
      trace_algebraMap]
    obtain ⟨n, hn⟩ := IsPurelyInseparable.finrank_eq_pow (separableClosure K L) L p
    cases n with
    | zero =>
      rw [pow_zero, IntermediateField.finrank_eq_one_iff_eq_top, separableClosure.eq_top_iff] at hn
      cases H hn
    | succ n =>
      cases hp with
      | zero =>
        rw [one_pow, IntermediateField.finrank_eq_one_iff_eq_top, separableClosure.eq_top_iff] at hn
        cases H hn
      | prime hprime =>
        rw [hn, pow_succ', SemigroupAction.mul_smul, LinearMap.map_smul_of_tower, nsmul_eq_mul,
          CharP.cast_eq_zero, zero_mul, LinearMap.zero_apply]
  · rw [trace_eq_finrank_mul_minpoly_nextCoeff]
    obtain ⟨g, hg₁, m, hg₂⟩ :=
      (minpoly.irreducible (IsIntegral.isIntegral (R := K) x)).hasSeparableContraction p
    cases m with
    | zero =>
      obtain rfl : g = minpoly K x := by simpa using hg₂
      cases hx hg₁
    | succ n =>
      rw [nextCoeff, if_neg, ← hg₂, coeff_expand (by positivity),
        if_neg, neg_zero, mul_zero, LinearMap.zero_apply]
      · rw [natDegree_expand]
        intro h
        have := Nat.dvd_sub (dvd_mul_left (p ^ (n + 1)) g.natDegree) h
        rw [tsub_tsub_cancel_of_le, Nat.dvd_one] at this
        · obtain rfl : g = minpoly K x := by simpa [this] using hg₂
          cases hx hg₁
        · rw [Nat.one_le_iff_ne_zero]
          have : g.natDegree ≠ 0 := fun e ↦ by
            have := congr(natDegree $hg₂)
            rw [natDegree_expand, e, zero_mul] at this
            exact (minpoly.natDegree_pos (IsIntegral.isIntegral x)).ne this
          positivity
      · exact (minpoly.natDegree_pos (IsIntegral.isIntegral x)).ne'

end NotIsSeparable

section DetNeZero

namespace Algebra

variable (A : Type u) {B : Type v} (C : Type z)

variable [CommRing A] [CommRing B] [Algebra A B] [CommRing C] [Algebra A C]

open Finset

noncomputable def traceMatrix (b : κ → B) : Matrix κ κ A :=
  of fun i j => traceForm A B (b i) (b j)
