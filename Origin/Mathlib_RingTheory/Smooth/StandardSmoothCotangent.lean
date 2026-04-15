/-
Extracted from RingTheory/Smooth/StandardSmoothCotangent.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Cotangent complex of a submersive presentation

Let `P` be a submersive presentation of `S` as an `R`-algebra and
denote by `I` the kernel `R[X] → S`. We show

- `SubmersivePresentation.free_cotangent`: `I ⧸ I ^ 2` is `S`-free on the classes of `P.relation i`.
- `SubmersivePresentation.subsingleton_h1Cotangent`: `H¹(L_{S/R}) = 0`.
- `SubmersivePresentation.free_kaehlerDifferential`: `Ω[S⁄R]` is `S`-free on the images of `dxᵢ`
  where `i ∉ Set.range P.map`.
- `SubmersivePresentation.rank_kaehlerDifferential`: If `S` is non-trivial, the rank of
  `Ω[S⁄R]` is the dimension of `P`.

We also provide the corresponding instances for standard smooth algebras as corollaries.

We keep the notation `I = ker(R[X] → S)` in all docstrings of this file.
-/

namespace Algebra

variable {R S ι σ : Type*} [CommRing R] [CommRing S] [Algebra R S]

open Extension Module MvPolynomial

namespace PreSubmersivePresentation

noncomputable def cotangentComplexAux [Finite σ] (P : PreSubmersivePresentation R S ι σ) :
    P.toExtension.Cotangent →ₗ[S] σ → S :=
  Finsupp.linearEquivFunOnFinite S S σ ∘ₗ Finsupp.lcomapDomain _ P.map_inj ∘ₗ
    P.cotangentSpaceBasis.repr.toLinearMap ∘ₗ P.toExtension.cotangentComplex

set_option backward.isDefEq.respectTransparency false in

lemma cotangentComplexAux_apply [Finite σ] (P : PreSubmersivePresentation R S ι σ)
    (x : P.ker) (i : σ) :
    P.cotangentComplexAux (Cotangent.mk x) i = (aeval P.val) (pderiv (P.map i) x.val) := by
  dsimp only [cotangentComplexAux, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    cotangentComplex_mk]
  simp only [Generators.toExtension_Ring, Finsupp.lcomapDomain_apply,
    Finsupp.linearEquivFunOnFinite_apply, Finsupp.comapDomain_apply,
    Generators.cotangentSpaceBasis_repr_tmul, one_mul]

lemma cotangentComplexAux_zero_iff [Finite σ] {P : PreSubmersivePresentation R S ι σ} (x : P.ker) :
    P.cotangentComplexAux (Cotangent.mk x) = 0 ↔
      ∀ i : σ, (aeval P.val) (pderiv (P.map i) x.val) = 0 := by
  rw [funext_iff]
  simp_rw [cotangentComplexAux_apply, Pi.zero_apply]

end PreSubmersivePresentation

namespace SubmersivePresentation

variable [Finite σ] (P : SubmersivePresentation R S ι σ)

set_option backward.isDefEq.respectTransparency false in

lemma cotangentComplexAux_injective [Finite σ] : Function.Injective P.cotangentComplexAux := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  obtain ⟨(x : P.ker), rfl⟩ := Cotangent.mk_surjective x
  rw [Submodule.mem_bot, Cotangent.mk_eq_zero_iff]
  rw [LinearMap.mem_ker, P.cotangentComplexAux_zero_iff] at hx
  have : x.val ∈ Ideal.span (Set.range P.relation) := by
    rw [P.span_range_relation_eq_ker]
    exact x.property
  obtain ⟨c, hc⟩ := Finsupp.mem_ideal_span_range_iff_exists_finsupp.mp this
  have heq (i : σ) :
      aeval P.val (pderiv (P.map i) <| c.sum fun i a ↦ a * P.relation i) = 0 := by
    rw [hc]
    apply hx
  simp only [Finsupp.sum, map_sum, Derivation.leibniz, smul_eq_mul, map_add, map_mul,
    Presentation.aeval_val_relation, zero_mul, add_zero] at heq
  have heq2 : ∑ i ∈ c.support,
      aeval P.val (c i) • (fun j ↦ aeval P.val (pderiv (P.map j) (P.relation i))) = 0 := by
    ext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    apply heq
  have (i : σ) : aeval P.val (c i) = 0 := by
    have := P.linearIndependent_aeval_val_pderiv_relation
    rw [linearIndependent_iff''] at this
    have := this c.support (fun i ↦ aeval P.val (c i))
      (by intro i; simp only [Finsupp.mem_support_iff, ne_eq, not_not]; intro h; simp [h]) heq2
    exact this i
  change _ ∈ P.ker ^ 2
  rw [← hc]
  apply Ideal.sum_mem
  intro i hi
  rw [pow_two]
  apply Ideal.mul_mem_mul
  · rw [P.ker_eq_ker_aeval_val]
    simpa using this i
  · exact P.relation_mem_ker i

lemma cotangentComplexAux_surjective [Finite σ] : Function.Surjective P.cotangentComplexAux := by
  rw [← LinearMap.range_eq_top, _root_.eq_top_iff, ← P.basisDeriv.span_eq, Submodule.span_le]
  rintro - ⟨i, rfl⟩
  use Cotangent.mk ⟨P.relation i, P.relation_mem_ker i⟩
  ext j
  rw [P.cotangentComplexAux_apply]
  simp
