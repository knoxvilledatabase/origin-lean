/-
Extracted from RingTheory/Kaehler/JacobiZariski.lean
Genuine: 12 of 13 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!

# The Jacobi-Zariski exact sequence

Given `R → S → T`, the Jacobi-Zariski exact sequence is
```
H¹(L_{T/R}) → H¹(L_{T/S}) → T ⊗[S] Ω[S/R] → Ω[T/R] → Ω[T/S] → 0
```
The maps are
- `Algebra.H1Cotangent.map`
- `Algebra.H1Cotangent.δ`
- `KaehlerDifferential.mapBaseChange`
- `KaehlerDifferential.map`

and the exactness lemmas are
- `Algebra.H1Cotangent.exact_map_δ`
- `Algebra.H1Cotangent.exact_δ_mapBaseChange`
- `KaehlerDifferential.exact_mapBaseChange_map`
- `KaehlerDifferential.map_surjective`
-/

open KaehlerDifferential Module MvPolynomial TensorProduct

namespace Algebra

universe w₁ w₂ w₃ w₄ w₅ u₁ u₂ u₃

variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] [Algebra R S]

variable {T : Type u₃} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

variable {ι : Type w₁} {ι' : Type w₃} {σ : Type w₂} {σ' : Type w₄} {τ : Type w₅}

variable (Q : Generators S T ι) (P : Generators R S σ)

variable (Q' : Generators S T ι') (P' : Generators R S σ') (W : Generators R T τ)

attribute [local instance] SMulCommClass.of_commMonoid

namespace Generators

set_option backward.isDefEq.respectTransparency false in

lemma Cotangent.surjective_map_ofComp :
    Function.Surjective (Extension.Cotangent.map (Q.ofComp P).toExtensionHom) := by
  intro x
  obtain ⟨⟨x, hx⟩, rfl⟩ := Extension.Cotangent.mk_surjective x
  have : x ∈ Q.ker := hx
  rw [← map_ofComp_ker Q P, Ideal.mem_map_iff_of_surjective
    _ (toAlgHom_ofComp_surjective Q P)] at this
  obtain ⟨x, hx', rfl⟩ := this
  exact ⟨.mk ⟨x, hx'⟩, Extension.Cotangent.map_mk _ _⟩

set_option backward.isDefEq.respectTransparency false in

open Extension.Cotangent in

lemma Cotangent.exact :
    Function.Exact
      ((Extension.Cotangent.map (Q.toComp P).toExtensionHom).liftBaseChange T)
      (Extension.Cotangent.map (Q.ofComp P).toExtensionHom) := by
  apply LinearMap.exact_of_comp_of_mem_range
  · rw [LinearMap.liftBaseChange_comp, ← Extension.Cotangent.map_comp,
      EmbeddingLike.map_eq_zero_iff]
    ext x
    obtain ⟨⟨x, hx⟩, rfl⟩ := Extension.Cotangent.mk_surjective x
    simp only [map_mk, val_mk, LinearMap.zero_apply, val_zero]
    convert Q.ker.toCotangent.map_zero
    trans ((IsScalarTower.toAlgHom R _ _).comp (IsScalarTower.toAlgHom R P.Ring S)) x
    · congr
      refine MvPolynomial.algHom_ext fun i ↦ ?_
      change (Q.ofComp P).toAlgHom ((Q.toComp P).toAlgHom (X i)) = _
      simp
    · simp [aeval_val_eq_zero hx]
  · intro x hx
    obtain ⟨⟨x : (Q.comp P).Ring, hx'⟩, rfl⟩ := Extension.Cotangent.mk_surjective x
    replace hx : (Q.ofComp P).toAlgHom x ∈ Q.ker ^ 2 := by
      simpa only [map_mk, val_mk, val_zero, Ideal.toCotangent_eq_zero] using congr(($hx).val)
    rw [pow_two, ← map_ofComp_ker (P := P), ← Ideal.map_mul, Ideal.mem_map_iff_of_surjective
      _ (toAlgHom_ofComp_surjective Q P)] at hx
    obtain ⟨y, hy, e⟩ := hx
    rw [eq_comm, ← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, ← map_toComp_ker] at e
    rw [LinearMap.range_liftBaseChange]
    let z : (Q.comp P).ker := ⟨x - y, Ideal.sub_mem _ hx' (Ideal.mul_le_left hy)⟩
    have hz : z.1 ∈ P.ker.map (Q.toComp P).toAlgHom.toRingHom := e
    have : Extension.Cotangent.mk (P := (Q.comp P).toExtension) ⟨x, hx'⟩ =
      Extension.Cotangent.mk z := by
      ext; simpa only [val_mk, Ideal.toCotangent_eq, sub_sub_cancel, pow_two, z]
    rw [this, ← Submodule.restrictScalars_mem (Q.comp P).Ring, ← Submodule.mem_comap,
      ← Submodule.span_singleton_le_iff_mem, ← Submodule.map_le_map_iff_of_injective
      (f := Submodule.subtype _) Subtype.val_injective, Submodule.map_subtype_span_singleton,
      Submodule.span_singleton_le_iff_mem]
    refine (show Ideal.map (Q.toComp P).toAlgHom.toRingHom P.ker ≤ _ from ?_) hz
    rw [Ideal.map_le_iff_le_comap]
    rintro w hw
    simp only [AlgHom.toRingHom_eq_coe, Ideal.mem_comap, RingHom.coe_coe,
      Submodule.mem_map, Submodule.mem_comap, Submodule.restrictScalars_mem, Submodule.coe_subtype,
      Subtype.exists, exists_and_right, exists_eq_right,
      toExtension_Ring]
    refine ⟨?_, Submodule.subset_span ⟨Extension.Cotangent.mk ⟨w, hw⟩, ?_⟩⟩
    · simp only [ker_eq_ker_aeval_val, RingHom.mem_ker, Hom.algebraMap_toAlgHom]
      rw [aeval_val_eq_zero hw, map_zero]
    · rw [map_mk]
      rfl

noncomputable

def CotangentSpace.compEquiv :
    (Q.comp P).toExtension.CotangentSpace ≃ₗ[T]
      Q.toExtension.CotangentSpace × (T ⊗[S] P.toExtension.CotangentSpace) :=
  (Q.comp P).cotangentSpaceBasis.repr.trans
    (Q.cotangentSpaceBasis.prod (P.cotangentSpaceBasis.baseChange T)).repr.symm

section instanceProblem

-- INSTANCE (free from Core): 999999]

lemma CotangentSpace.compEquiv_symm_inr :
    (compEquiv Q P).symm.toLinearMap ∘ₗ
      LinearMap.inr T Q.toExtension.CotangentSpace (T ⊗[S] P.toExtension.CotangentSpace) =
        (Extension.CotangentSpace.map (Q.toComp P).toExtensionHom).liftBaseChange T := by
  classical
  apply (P.cotangentSpaceBasis.baseChange T).ext
  intro i
  apply (Q.comp P).cotangentSpaceBasis.repr.injective
  ext j
  simp only [compEquiv, LinearEquiv.trans_symm, LinearEquiv.symm_symm,
    Basis.baseChange_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, LinearMap.coe_inr,
    Function.comp_apply, LinearEquiv.trans_apply, Basis.repr_symm_apply, pderiv_X, toComp_val,
    Basis.repr_linearCombination, LinearMap.liftBaseChange_tmul, one_smul, repr_CotangentSpaceMap]
  obtain (j | j) := j <;>
    simp only [Basis.prod_repr_inr, Basis.baseChange_repr_tmul,
      Basis.repr_self, Basis.prod_repr_inl, map_zero, Finsupp.coe_zero,
      Pi.zero_apply, ne_eq, not_false_eq_true, Pi.single_eq_of_ne, Pi.single_apply,
      Finsupp.single_apply, ite_smul, one_smul, zero_smul, Sum.inr.injEq,
      MonoidWithZeroHom.map_ite_one_zero, reduceCtorEq]

lemma CotangentSpace.compEquiv_symm_zero (x) :
    (compEquiv Q P).symm (0, x) =
        (Extension.CotangentSpace.map (Q.toComp P).toExtensionHom).liftBaseChange T x :=
  DFunLike.congr_fun (compEquiv_symm_inr Q P) x

lemma CotangentSpace.fst_compEquiv :
    LinearMap.fst T Q.toExtension.CotangentSpace (T ⊗[S] P.toExtension.CotangentSpace) ∘ₗ
      (compEquiv Q P).toLinearMap = Extension.CotangentSpace.map (Q.ofComp P).toExtensionHom := by
  classical
  apply (Q.comp P).cotangentSpaceBasis.ext
  intro i
  apply Q.cotangentSpaceBasis.repr.injective
  ext j
  simp only [compEquiv, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, ofComp_val,
    LinearEquiv.trans_apply, Basis.repr_self, LinearMap.fst_apply, repr_CotangentSpaceMap]
  obtain (i | i) := i <;>
    simp only [Basis.repr_symm_apply, Finsupp.linearCombination_single, Basis.prod_apply,
      LinearMap.coe_inl, LinearMap.coe_inr, Sum.elim_inl, Function.comp_apply, one_smul,
      Basis.repr_self, Finsupp.single_apply, pderiv_X, Pi.single_apply,
      Sum.elim_inr, Function.comp_apply, Basis.baseChange_apply, one_smul,
      MonoidWithZeroHom.map_ite_one_zero, map_zero, Finsupp.coe_zero, Pi.zero_apply, derivation_C]

lemma CotangentSpace.fst_compEquiv_apply (x) :
    (compEquiv Q P x).1 = Extension.CotangentSpace.map (Q.ofComp P).toExtensionHom x :=
  DFunLike.congr_fun (fst_compEquiv Q P) x

lemma CotangentSpace.map_toComp_injective :
    Function.Injective
      ((Extension.CotangentSpace.map (Q.toComp P).toExtensionHom).liftBaseChange T) := by
  rw [← compEquiv_symm_inr]
  apply (compEquiv Q P).symm.injective.comp
  exact Prod.mk_right_injective _

lemma CotangentSpace.map_ofComp_surjective :
    Function.Surjective (Extension.CotangentSpace.map (Q.ofComp P).toExtensionHom) := by
  rw [← fst_compEquiv]
  exact (Prod.fst_surjective).comp (compEquiv Q P).surjective

/-!
Given representations `R[X] → S` and `S[Y] → T`, the sequence
`T ⊗[S] (⨁ₓ S dx) → (⨁ₓ T dx) ⊕ (⨁ᵧ T dy) → ⨁ᵧ T dy`
is exact.
-/

lemma CotangentSpace.exact :
    Function.Exact ((Extension.CotangentSpace.map (Q.toComp P).toExtensionHom).liftBaseChange T)
      (Extension.CotangentSpace.map (Q.ofComp P).toExtensionHom) := by
  rw [← fst_compEquiv, ← compEquiv_symm_inr]
  conv_rhs => rw [← LinearEquiv.symm_symm (compEquiv Q P)]
  rw [LinearEquiv.conj_exact_iff_exact]
  exact Function.Exact.inr_fst

namespace H1Cotangent

variable (R) in

noncomputable

def δAux :
    Q.Ring →ₗ[R] T ⊗[S] Ω[S⁄R] :=
  Finsupp.lsum R (R := R) fun f ↦
    (TensorProduct.mk S T _ (f.prod (Q.val · ^ ·))).restrictScalars R ∘ₗ (D R S).toLinearMap

lemma δAux_monomial (n r) :
    δAux R Q (monomial n r) = (n.prod (Q.val · ^ ·)) ⊗ₜ D R S r :=
  Finsupp.lsum_single _ _ _ _
