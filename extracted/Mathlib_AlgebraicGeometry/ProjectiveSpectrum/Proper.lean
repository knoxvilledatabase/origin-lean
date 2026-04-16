/-
Extracted from AlgebraicGeometry/ProjectiveSpectrum/Proper.lean
Genuine: 1 | Conflates: 0 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

noncomputable section

/-!
# Properness of `Proj A`

We show that `Proj 𝒜` is a separated scheme.

## TODO
- Show that `Proj 𝒜` satisfies the valuative criterion.

## Notes
This contribution was created as part of the Durham Computational Algebraic Geometry Workshop

-/

namespace AlgebraicGeometry.Proj

variable {R A : Type*}

variable [CommRing R] [CommRing A] [Algebra R A]

variable (𝒜 : ℕ → Submodule R A)

variable [GradedAlgebra 𝒜]

open Scheme CategoryTheory Limits pullback HomogeneousLocalization

lemma lift_awayMapₐ_awayMapₐ_surjective {d e : ℕ} {f : A} (hf : f ∈ 𝒜 d)
    {g : A} (hg : g ∈ 𝒜 e) {x : A} (hx : x = f * g) (hd : 0 < d) :
    Function.Surjective
      (Algebra.TensorProduct.lift (awayMapₐ 𝒜 hg hx) (awayMapₐ 𝒜 hf (hx.trans (mul_comm _ _)))
        (fun _ _ ↦ .all _ _)) := by
  intro z
  obtain ⟨⟨n, ⟨a, ha⟩, ⟨b, hb'⟩, ⟨j, (rfl : _ = b)⟩⟩, rfl⟩ := mk_surjective z
  by_cases hfg : (f * g) ^ j = 0
  · use 0
    have := HomogeneousLocalization.subsingleton 𝒜 (x := Submonoid.powers x) ⟨j, hx ▸ hfg⟩
    exact this.elim _ _
  have : n = j * (d + e) := by
    apply DirectSum.degree_eq_of_mem_mem 𝒜 hb'
    convert SetLike.pow_mem_graded _ _ using 2
    · infer_instance
    · exact hx ▸ SetLike.mul_mem_graded hf hg
    · exact hx ▸ hfg
  let x0 : NumDenSameDeg 𝒜 (.powers f) :=
  { deg := j * (d * (e + 1))
    num := ⟨a * g ^ (j * (d - 1)), by
      convert SetLike.mul_mem_graded ha (SetLike.pow_mem_graded _ hg) using 2
      rw [this]
      cases d
      · contradiction
      · simp; ring⟩
    den := ⟨f ^ (j * (e + 1)), by convert SetLike.pow_mem_graded _ hf using 2; ring⟩
    den_mem := ⟨_,rfl⟩ }
  let y0 : NumDenSameDeg 𝒜 (.powers g) :=
  { deg := j * (d * e)
    num := ⟨f ^ (j * e), by convert SetLike.pow_mem_graded _ hf using 2; ring⟩
    den := ⟨g ^ (j * d), by convert SetLike.pow_mem_graded _ hg using 2; ring⟩
    den_mem := ⟨_,rfl⟩ }
  use mk x0 ⊗ₜ mk y0
  ext
  simp only [Algebra.TensorProduct.lift_tmul, awayMapₐ_apply, val_mul,
    val_awayMap_mk, Localization.mk_mul, val_mk, x0, y0]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  use 1
  simp only [OneMemClass.coe_one, one_mul, Submonoid.mk_mul_mk]
  cases d
  · contradiction
  · simp only [hx, add_tsub_cancel_right]
    ring

open TensorProduct in

instance isSeparated : IsSeparated (toSpecZero 𝒜) := by
  refine ⟨IsLocalAtTarget.of_openCover (Pullback.openCoverOfLeftRight
    (affineOpenCover 𝒜).openCover (affineOpenCover 𝒜).openCover _ _) ?_⟩
  intro ⟨i, j⟩
  dsimp [Scheme, Cover.pullbackHom]
  refine (MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion)
    (f := (pullbackDiagonalMapIdIso ..).inv) _).mp ?_
  let e₁ : pullback ((affineOpenCover 𝒜).map i ≫ toSpecZero 𝒜)
        ((affineOpenCover 𝒜).map j ≫ toSpecZero 𝒜) ≅
        Spec (.of <| TensorProduct (𝒜 0) (Away 𝒜 i.2) (Away 𝒜 j.2)) := by
    refine pullback.congrHom ?_ ?_ ≪≫ pullbackSpecIso (𝒜 0) (Away 𝒜 i.2) (Away 𝒜 j.2)
    · simp [affineOpenCover, openCoverOfISupEqTop, awayι_toSpecZero]; rfl
    · simp [affineOpenCover, openCoverOfISupEqTop, awayι_toSpecZero]; rfl
  let e₂ : pullback ((affineOpenCover 𝒜).map i) ((affineOpenCover 𝒜).map j) ≅
        Spec (.of <| (Away 𝒜 (i.2 * j.2))) :=
    pullbackAwayιIso 𝒜 _ _ _ _ rfl
  rw [← MorphismProperty.cancel_right_of_respectsIso (P := @IsClosedImmersion) _ e₁.hom,
    ← MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion) e₂.inv]
  let F : Away 𝒜 i.2.1 ⊗[𝒜 0] Away 𝒜 j.2.1 →+* Away 𝒜 (i.2.1 * j.2.1) :=
    (Algebra.TensorProduct.lift (awayMapₐ 𝒜 j.2.2 rfl) (awayMapₐ 𝒜 i.2.2 (mul_comm _ _))
      (fun _ _ ↦ .all _ _)).toRingHom
  have : Function.Surjective F := lift_awayMapₐ_awayMapₐ_surjective 𝒜 i.2.2 j.2.2 rfl i.1.2
  convert IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (R := Away 𝒜 i.2.1 ⊗[𝒜 0] Away 𝒜 j.2.1) F) this using 1
  rw [← cancel_mono (pullbackSpecIso ..).inv]
  apply pullback.hom_ext
  · simp only [Iso.trans_hom, congrHom_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id,
      limit.lift_π, id_eq, eq_mpr_eq_cast, PullbackCone.mk_pt, PullbackCone.mk_π_app, e₂, e₁,
      pullbackDiagonalMapIdIso_inv_snd_fst, AlgHom.toRingHom_eq_coe, pullbackSpecIso_inv_fst,
      ← Spec.map_comp]
    erw [pullbackAwayιIso_inv_fst]
    congr 1
    ext x
    exact DFunLike.congr_fun (Algebra.TensorProduct.lift_comp_includeLeft
      (awayMapₐ 𝒜 j.2.2 rfl) (awayMapₐ 𝒜 i.2.2 (mul_comm _ _)) (fun _ _ ↦ .all _ _)).symm x
  · simp only [Iso.trans_hom, congrHom_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id,
      limit.lift_π, id_eq, eq_mpr_eq_cast, PullbackCone.mk_pt, PullbackCone.mk_π_app,
      pullbackDiagonalMapIdIso_inv_snd_snd, AlgHom.toRingHom_eq_coe, pullbackSpecIso_inv_snd, ←
      Spec.map_comp, e₂, e₁]
    erw [pullbackAwayιIso_inv_snd]
    congr 1
    ext x
    exact DFunLike.congr_fun (Algebra.TensorProduct.lift_comp_includeRight
      (awayMapₐ 𝒜 j.2.2 rfl) (awayMapₐ 𝒜 i.2.2 (mul_comm _ _)) (fun _ _ ↦ .all _ _)).symm x

@[stacks 01MC]
instance : Scheme.IsSeparated (Proj 𝒜) :=
  (HasAffineProperty.iff_of_isAffine (P := @IsSeparated)).mp (isSeparated 𝒜)

end AlgebraicGeometry.Proj
