/-
Extracted from RingTheory/Smooth/Quotient.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!

# Some lemmas about formally smooth under quotient

In this file, we formalize the result [Stacks 031L] : For flat ring homomorphism `f : R →+* S`,
`I` an ideal of `R` which is square zero, if `R ⧸ I →+* S ⧸ IS` is formally smooth, so is `f`.

-/

open IsLocalRing

variable {R : Type*} [CommRing R]

lemma LinearMap.ker_inf_smul_top_eq_smul_of_flat {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (I : Ideal R) (f : M →ₗ[R] N) (surj : Function.Surjective f)
    [Module.Flat R N] : f.ker ⊓ (I • (⊤ : Submodule R M)) = I • f.ker := by
  refine le_antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · rcases (Submodule.ext_iff.mp (I.subtype_rTensor_range M) x).mpr hx.2 with ⟨y, hy⟩
    have inj : Function.Injective ((TensorProduct.lid R N).comp (I.subtype.rTensor N)) := by
      simpa using Module.Flat.iff_rTensor_injective'.mp ‹_› I
    have comm1 : ((TensorProduct.lid R N).comp (I.subtype.rTensor N)).comp (f.lTensor I) =
      f.comp ((TensorProduct.lid R M).comp (I.subtype.rTensor M)) := by
      ext
      simp
    have eq0 : f.lTensor I y = 0 := by
      apply inj
      rw [map_zero, ← LinearMap.comp_apply, comm1, LinearMap.comp_apply, hy, f.mem_ker.mp hx.1]
    rcases ((lTensor_exact I (f.exact_subtype_ker_map) surj) y).mp eq0 with ⟨z, hz⟩
    have comm2 : ((TensorProduct.lid R M).comp (I.subtype.rTensor M)).comp
      (f.ker.subtype.lTensor I) = f.ker.subtype.comp
      ((TensorProduct.lid R f.ker).comp (I.subtype.rTensor f.ker)) := by
      ext
      simp
    apply (Submodule.mem_smul_top_iff I f.ker ⟨x, hx.1⟩).mp
    rw [← Ideal.subtype_rTensor_range]
    use z
    apply f.ker.subtype_injective
    rw [← LinearMap.comp_apply, ← comm2, LinearMap.comp_apply, hz, hy, Submodule.subtype_apply]
  · induction hx using Submodule.smul_induction_on' with
    | smul r hr m hm =>
      simpa [LinearMap.mem_ker.mp hm] using Submodule.smul_mem_smul hr Submodule.mem_top
    | add y ymem z zmem hy hz => exact add_mem hy hz

variable {S : Type*} [CommRing S] {R' S' : Type*} [CommRing R'] [CommRing S']

variable [Algebra R S] [Algebra R R'] [Algebra R' S'] [Algebra S S']
    [Algebra R S'] [IsScalarTower R S S'] [IsScalarTower R R' S']

private lemma comap_ker_eq_sup_of_ker_eq_map (surjRS : Function.Surjective (algebraMap R S))
    (eqmap : RingHom.ker (algebraMap S S') = (RingHom.ker (algebraMap R R')).map (algebraMap R S)) :
    (RingHom.ker (algebraMap R' S')).comap (algebraMap R R') =
      RingHom.ker (algebraMap R R') ⊔ RingHom.ker (algebraMap R S) := by
  rw [RingHom.comap_ker, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq _ S,
      ← RingHom.comap_ker]
  simp [eqmap, Ideal.comap_map_of_surjective' _ surjRS]
