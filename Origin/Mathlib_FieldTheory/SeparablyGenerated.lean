/-
Extracted from FieldTheory/SeparablyGenerated.lean
Genuine: 6 of 10 | Dissolved: 3 | Infrastructure: 1
-/
import Origin.Core

/-!

# Separably generated extensions

We aim to formalize the following result:

Let `K/k` be a finitely generated field extension with characteristic `p > 0`, then TFAE
1. `K/k` is separably generated
2. If `{ sᵢ } ⊆ K` is an arbitrary `k`-linearly independent set,
  `{ sᵢᵖ } ⊆ K` is also `k`-linearly independent
3. `K ⊗ₖ k^{1/p}` is reduced
4. `K` is geometrically reduced over `k`.
5. `k` and `Kᵖ` are linearly disjoint over `kᵖ` in `K`.

## Main result
- `exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow`: (2) ⇒ (1)

-/

-- INSTANCE (free from Core): 2000]

open MvPolynomial

open scoped IntermediateField

variable {k K ι : Type*} [Field k] [Field K] [Algebra k K] (p : ℕ) (hp : p.Prime)

variable (H : ∀ s : Finset K,
  LinearIndepOn k _root_.id (s : Set K) → LinearIndepOn k (· ^ p) (s : Set K))

variable {a : ι → K} (n : ι)

namespace MvPolynomial

def toPolynomialAdjoinImageCompl (F : MvPolynomial ι k) (a : ι → K) (i : ι) :
    Polynomial (Algebra.adjoin k (a '' {i}ᶜ)) :=
  letI := Classical.typeDecidableEq ι
  (optionEquivLeft k _ (renameEquiv k (Equiv.optionSubtypeNe i).symm F)).mapAlgHom
    (aeval fun j : {j // j ≠ i} ↦
      (⟨a j, Algebra.subset_adjoin ⟨j, j.2, rfl⟩⟩ : Algebra.adjoin k (a '' {i}ᶜ)))

theorem aeval_toPolynomialAdjoinImageCompl_eq_zero
    {a : ι → K} {F : MvPolynomial ι k} (hFa : F.aeval a = 0) (i : ι) :
    (toPolynomialAdjoinImageCompl F a i).aeval (a i) = 0 := by
  rw [← hFa, ← AlgHom.restrictScalars_apply k]
  simp_rw [toPolynomialAdjoinImageCompl, ← AlgEquiv.coe_algHom, ← AlgHom.comp_apply]
  congr; ext; aesop (add simp optionEquivLeft_X_some) (add simp optionEquivLeft_X_none)

set_option backward.isDefEq.respectTransparency false in

theorem irreducible_toPolynomialAdjoinImageCompl {F : MvPolynomial ι k} (hF : Irreducible F) (i : ι)
    (H : AlgebraicIndependent k fun x : {j | j ≠ i} ↦ a x) :
    Irreducible (toPolynomialAdjoinImageCompl F a i) := by
  have : a '' {i}ᶜ = Set.range (fun x : {j | j ≠ i} ↦ a x) := by ext; simp
  delta toPolynomialAdjoinImageCompl
  convert hF.map (renameEquiv k (Equiv.optionSubtypeNe i).symm) |>.map (optionEquivLeft k _) |>.map
    (Polynomial.mapAlgEquiv (H.aevalEquiv.trans
      (Subalgebra.equivOfEq _ _ congr(Algebra.adjoin k $this.symm))))
  rw [← AlgEquiv.coe_algHom]
  congr
  aesop

variable {F : MvPolynomial ι k}

variable (HF : ∀ F' : MvPolynomial ι k, F' ≠ 0 → F'.aeval a = 0 → F.totalDegree ≤ F'.totalDegree)

include HF

-- DISSOLVED: irreducible_of_forall_totalDegree_le

-- DISSOLVED: coeff_toPolynomialAdjoinImageCompl_ne_zero

theorem isAlgebraic_of_mem_vars_of_forall_totalDegree_le (hFa : F.aeval a = 0) (i : ι)
    (hi : i ∈ F.vars) : IsAlgebraic (Algebra.adjoin k (a '' {i}ᶜ)) (a i) := by
  classical
  have ⟨σ, hσ, hσi⟩ := (mem_vars i).mp hi
  refine ⟨toPolynomialAdjoinImageCompl F a i,
    fun h ↦ coeff_toPolynomialAdjoinImageCompl_ne_zero HF σ hσ i
      (Finsupp.mem_support_iff.mp hσi) ?_, aeval_toPolynomialAdjoinImageCompl_eq_zero hFa ..⟩
  rw [h, Polynomial.coeff_zero]

set_option backward.isDefEq.respectTransparency false in

include hp H in

-- DISSOLVED: exists_mem_support_not_dvd_of_forall_totalDegree_le

end MvPolynomial

open IntermediateField

variable [ExpChar k p]

include hp H

lemma exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow
    (ha' : IsTranscendenceBasis k fun i : {i // i ≠ n} ↦ a i) :
    ∃ i : ι, IsTranscendenceBasis k (fun j : {j // j ≠ i} ↦ a j) ∧
      IsSeparable (adjoin k (a '' {i}ᶜ)) (a i) := by
  set S := {F : MvPolynomial ι k | F ≠ 0 ∧ F.aeval a = 0}
  obtain ⟨F, ⟨hF₀, hFa⟩, hFmin⟩ :
      ∃ F ∈ S, ∀ G : MvPolynomial ι k, G ≠ 0 → G.aeval a = 0 → totalDegree F ≤ totalDegree G := by
    suffices S.Nonempty from
      ⟨totalDegree.argminOn S this, totalDegree.argminOn_mem ..,
        fun _ h₁ h₂ ↦ totalDegree.argminOn_le S ⟨h₁, h₂⟩⟩
    suffices ¬ AlgebraicIndependent k a by simpa [S, algebraicIndependent_iff, and_comm] using this
    intro h
    refine h.transcendental_adjoin (i := n) (s := {n}ᶜ) (by simp) ?_
    have : a '' {n}ᶜ = Set.range (ι := {i // i ≠ n}) (a ·) := by aesop
    convert ha'.isAlgebraic.isAlgebraic _
  have hFirr : Irreducible F := irreducible_of_forall_totalDegree_le hFmin hF₀ hFa
  obtain ⟨i, σ, hσ, hi⟩ := exists_mem_support_not_dvd_of_forall_totalDegree_le p hp H hFmin hF₀ hFa
  have hσi : σ i ≠ 0 := by aesop
  have alg := isAlgebraic_of_mem_vars_of_forall_totalDegree_le hFmin hFa i <|
    (mem_vars i).mpr ⟨σ, hσ, by simpa⟩
  have Hi := ha'.of_isAlgebraic_adjoin_image_compl _ i _ alg
  refine ⟨i, Hi, ?_⟩
  let k' := adjoin k (a '' {i}ᶜ)
  have hF₁irr := irreducible_toPolynomialAdjoinImageCompl hFirr i Hi.1
  have := (AlgebraicIndepOn.aevalEquiv (s := {i}ᶜ) Hi.1).uniqueFactorizationMonoid inferInstance
  have coeff_ne := coeff_toPolynomialAdjoinImageCompl_ne_zero hFmin σ hσ i hσi
  open scoped algebraAdjoinAdjoin in
  have hF₂irr := (hF₁irr.isPrimitive fun h ↦ coeff_ne <| Polynomial.coeff_eq_zero_of_natDegree_lt <|
    h.trans_lt <| Nat.pos_iff_ne_zero.2 hσi).irreducible_iff_irreducible_map_fraction_map
    (K := k').1 hF₁irr
  contrapose coeff_ne with Hsep
  have : CharP k' p := (expChar_of_injective_algebraMap (algebraMap k k').injective p).casesOn
    (fun e ↦ (e rfl).elim) (fun _ _ _ ↦ ‹_›) hp.ne_one
  obtain ⟨g, hg, eq⟩ := (((minpoly k' (a i)).separable_or p (minpoly.irreducible
    (isAlgebraic_iff_isIntegral.mp <| isAlgebraic_adjoin_iff.mpr alg))).resolve_left Hsep).2
  replace eq := congr(Polynomial.coeff $eq (σ i))
  rwa [← minpoly.eq_of_irreducible hF₂irr ((Polynomial.aeval_map_algebraMap ..).trans
    (aeval_toPolynomialAdjoinImageCompl_eq_zero hFa i)), Polynomial.coeff_mul_C,
    Polynomial.coeff_expand hp.pos, if_neg hi, eq_mul_inv_iff_mul_eq₀
    (by simpa using hF₂irr.ne_zero), zero_mul, eq_comm,
    Polynomial.coeff_map, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective ..)] at eq

lemma exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow'
    (s : Set ι) (n : ι) (ha : IsTranscendenceBasis k fun i : s ↦ a i) (hn : n ∉ s) :
    ∃ i : ι, IsTranscendenceBasis k (fun j : ↥(insert n s \ {i}) ↦ a j) ∧
      IsSeparable (adjoin k (a '' (insert n s \ {i}))) (a i) := by
  let e₁ : {j : ↥(insert n s) // j ≠ ⟨n, by simp⟩} ≃ ↑s :=
    ⟨fun x ↦ ⟨x, by aesop⟩, fun x ↦ ⟨⟨x, by aesop⟩, by aesop⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩
  obtain ⟨i, hi, hi'⟩ := exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow p hp H
    (a := fun i : ↥(insert n s) ↦ a i) ⟨n, by simp⟩ (ha.comp_equiv e₁)
  let e₂ : {j // j ≠ i} ≃ ↥(insert n s \ {i.1}) := ⟨fun x ↦ ⟨x, x.1.2, fun h ↦ x.2 (Subtype.ext h)⟩,
    fun x ↦ ⟨⟨x, x.2.1⟩, fun h ↦ x.2.2 congr($h.1)⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩
  have : a '' (insert n s \ {i.1}) = (a ·.1) '' {i}ᶜ := by ext; aesop
  refine ⟨i, hi.comp_equiv e₂.symm, by convert hi'⟩
