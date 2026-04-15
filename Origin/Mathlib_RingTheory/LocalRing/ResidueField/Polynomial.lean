/-
Extracted from RingTheory/LocalRing/ResidueField/Polynomial.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Residue field of primes in polynomial algebras

## Main results
- `Polynomial.residueFieldMapCAlgEquiv`: `κ(I[X]) ≃ₐ[κ(I)] κ(I)(X)`
- `Polynomial.fiberEquivQuotient`: `κ(p) ⊗[R] (R[X] ⧸ I) = κ(p)[X] / I`

-/

namespace Polynomial

open scoped nonZeroDivisors TensorProduct

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

variable (I : Ideal R) [I.IsPrime] (J : Ideal R[X]) [J.IsPrime]

noncomputable

def residueFieldMapCAlgEquiv [J.LiesOver I] (hJ : J = I.map C) :
    J.ResidueField ≃ₐ[I.ResidueField] RatFunc I.ResidueField := by
  letI f : J.ResidueField →+* RatFunc I.ResidueField := by
    refine Ideal.ResidueField.lift _
        ((algebraMap I.ResidueField[X] _).comp (mapRingHom (algebraMap _ _))) ?_ ?_
    · simp [hJ, Ideal.map_le_iff_le_comap, RingHom.comap_ker _ C, mapRingHom_comp_C,
        RingHom.ker_comp_of_injective, C_injective,
        FaithfulSMul.algebraMap_injective I.ResidueField[X] (RatFunc I.ResidueField)]
    · rintro x (hx : x ∉ J)
      suffices ∃ i, x.coeff i ∉ I by simpa [IsUnit.mem_submonoid_iff, Polynomial.ext_iff]
      contrapose! hx
      rwa [hJ, Ideal.mem_map_C_iff]
  haveI hf : f.comp (algebraMap I.ResidueField _) = algebraMap _ _ := by
    ext
    simp [f, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R R[X] J.ResidueField]
  refine .ofAlgHom ⟨f, fun r ↦ congr($hf r)⟩
      (RatFunc.liftAlgHom (aeval (algebraMap R[X] _ X)) fun x ↦ ?_) ?_ ?_
  · suffices Function.Injective (aeval (R := I.ResidueField) (algebraMap R[X] J.ResidueField X)) by
      simp [← this.eq_iff]
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨r, hr⟩ := map_surjective _ Ideal.Quotient.mk_surjective
      (IsLocalization.integerNormalization (R ⧸ I)⁰ x)
    obtain ⟨s, hs, hr⟩ : ∃ s ∉ I, r.map (algebraMap _ _) = s • x := by
      obtain ⟨b, hb0, hb⟩ := IsLocalization.integerNormalization_spec (R ⧸ I)⁰ x
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective b
      refine ⟨s, by simpa [Ideal.Quotient.eq_zero_iff_mem] using hb0, ?_⟩
      simpa [← hr, map_map, ← Ideal.Quotient.algebraMap_eq] using hb
    replace hx : r ∈ J := by
      apply_fun aeval (algebraMap R[X] J.ResidueField X) at hr
      simpa [hx, aeval_map_algebraMap, aeval_algebraMap_apply, Algebra.smul_def] using hr
    refine ((IsUnit.mk0 (algebraMap R I.ResidueField s) (by simpa)).map C).mul_right_injective ?_
    simp only [← algebraMap_eq, ← Algebra.smul_def, algebraMap_smul, ← hr]
    simpa [Polynomial.ext_iff, Ideal.mem_map_C_iff] using hJ.le hx
  · apply AlgHom.coe_ringHom_injective
    apply IsFractionRing.injective_comp_algebraMap (A := I.ResidueField[X])
    dsimp [RatFunc.liftAlgHom]
    simp only [AlgHom.comp_toRingHom, AlgHom.coe_ringHom_mk, RingHom.comp_assoc,
      RatFunc.liftRingHom_comp_algebraMap, RingHomCompTriple.comp_eq, f]
    ext <;> simp [← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply R R[X] J.ResidueField]
  · apply AlgHom.coe_ringHom_injective
    ext
    · simp [f, RatFunc.liftAlgHom, ← IsScalarTower.algebraMap_apply]; rfl
    · simp [f, RatFunc.liftAlgHom]
