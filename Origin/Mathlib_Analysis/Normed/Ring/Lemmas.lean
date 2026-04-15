/-
Extracted from Analysis/Normed/Ring/Lemmas.lean
Genuine: 4 of 26 | Dissolved: 4 | Infrastructure: 18
-/
import Origin.Core

/-!
# Normed rings

In this file we continue building the theory of (semi)normed rings.
-/

variable {α : Type*} {β : Type*} {ι : Type*}

open Filter Bornology

open scoped Topology NNReal Pointwise

section NonUnitalSeminormedRing

variable [NonUnitalSeminormedRing α]

-- DISSOLVED: Filter.Tendsto.zero_mul_isBoundedUnder_le

theorem Filter.isBoundedUnder_le_mul_tendsto_zero {f g : ι → α} {l : Filter ι}
    (hf : IsBoundedUnder (· ≤ ·) l (norm ∘ f)) (hg : Tendsto g l (𝓝 0)) :
    Tendsto (fun x => f x * g x) l (𝓝 0) :=
  hg.op_zero_isBoundedUnder_le hf (flip (· * ·)) fun x y =>
    (norm_mul_le y x).trans_eq (mul_comm _ _)

open Finset in

-- INSTANCE (free from Core): Pi.nonUnitalSeminormedRing

end NonUnitalSeminormedRing

section SeminormedRing

variable [SeminormedRing α]

-- INSTANCE (free from Core): Pi.seminormedRing

lemma RingHom.isometry {𝕜₁ 𝕜₂ : Type*} [SeminormedRing 𝕜₁] [SeminormedRing 𝕜₂]
    (σ : 𝕜₁ →+* 𝕜₂) [RingHomIsometric σ] :
    Isometry σ := AddMonoidHomClass.isometry_of_norm _ fun _ => RingHomIsometric.norm_map

lemma RingHomIsometric.inv {𝕜₁ 𝕜₂ : Type*} [SeminormedRing 𝕜₁] [SeminormedRing 𝕜₂]
    (σ : 𝕜₁ →+* 𝕜₂) {σ' : 𝕜₂ →+* 𝕜₁} [RingHomInvPair σ σ'] [RingHomIsometric σ] :
    RingHomIsometric σ' :=
  ⟨fun {x} ↦ by rw [← RingHomIsometric.norm_map (σ := σ), RingHomInvPair.comp_apply_eq₂]⟩

-- DISSOLVED: tendsto_pow_cobounded_cobounded

end SeminormedRing

section NonUnitalNormedRing

variable [NonUnitalNormedRing α]

-- INSTANCE (free from Core): Pi.nonUnitalNormedRing

end NonUnitalNormedRing

section NormedRing

variable [NormedRing α]

-- INSTANCE (free from Core): Pi.normedRing

end NormedRing

section NonUnitalSeminormedCommRing

variable [NonUnitalSeminormedCommRing α]

-- INSTANCE (free from Core): Pi.nonUnitalSeminormedCommRing

end NonUnitalSeminormedCommRing

section NonUnitalNormedCommRing

variable [NonUnitalNormedCommRing α]

-- INSTANCE (free from Core): Pi.nonUnitalNormedCommRing

end NonUnitalNormedCommRing

section SeminormedCommRing

variable [SeminormedCommRing α]

-- INSTANCE (free from Core): Pi.seminormedCommRing

end SeminormedCommRing

section NormedCommRing

variable [NormedCommRing α]

-- INSTANCE (free from Core): Pi.normedCommutativeRing

end NormedCommRing

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

namespace SeparationQuotient

-- INSTANCE (free from Core): [NonUnitalSeminormedRing

-- INSTANCE (free from Core): [NonUnitalSeminormedCommRing

-- INSTANCE (free from Core): [SeminormedRing

-- INSTANCE (free from Core): [SeminormedCommRing

-- INSTANCE (free from Core): [SeminormedAddCommGroup

end SeparationQuotient

namespace NNReal

lemma lipschitzWith_sub : LipschitzWith 2 (fun (p : ℝ≥0 × ℝ≥0) ↦ p.1 - p.2) := by
  rw [← NNReal.isometry_coe.lipschitzWith_iff]
  have : Isometry (Prod.map ((↑) : ℝ≥0 → ℝ) ((↑) : ℝ≥0 → ℝ)) :=
    NNReal.isometry_coe.prodMap NNReal.isometry_coe
  convert (((LipschitzWith.prod_fst.comp this.lipschitz).sub
    (LipschitzWith.prod_snd.comp this.lipschitz)).max_const 0)
  norm_num

end NNReal

-- INSTANCE (free from Core): Int.instNormedCommRing

-- INSTANCE (free from Core): Int.instNormOneClass

-- INSTANCE (free from Core): Int.instNormMulClass

section NonUnitalNormedRing

variable [NonUnitalNormedRing α] [NormMulClass α] {a : α}

-- DISSOLVED: antilipschitzWith_mul_left

-- DISSOLVED: antilipschitzWith_mul_right
