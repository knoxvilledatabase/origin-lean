/-
Extracted from AlgebraicGeometry/ProjectiveSpectrum/Proper.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Properness of `Proj A`

We show that `Proj 𝒜` is proper over `Spec 𝒜₀`.

## Notes
This contribution was created as part of the Durham Computational Algebraic Geometry Workshop

-/

namespace AlgebraicGeometry.Proj

variable {σ A : Type*}

variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]

variable (𝒜 : ℕ → σ)

variable [GradedRing 𝒜]

open Scheme CategoryTheory Limits pullback HomogeneousLocalization

section IsSeparated

set_option backward.isDefEq.respectTransparency false in

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
    · convert SetLike.pow_mem_graded _ _ using 2
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

set_option backward.isDefEq.respectTransparency false in

open TensorProduct in

-- INSTANCE (free from Core): isSeparated
