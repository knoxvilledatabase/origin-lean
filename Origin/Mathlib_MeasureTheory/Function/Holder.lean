/-
Extracted from MeasureTheory/Function/Holder.lean
Genuine: 11 of 11 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Continuous bilinear maps on `MeasureTheory.Lp` spaces

Given a continuous bilinear map `B : E →L[𝕜] F →L[𝕜] G`, we define an associated map
`ContinuousLinearMap.holder : Lp E p μ → Lp F q μ → Lp G r μ` where `p q r` are a Hölder triple.
We bundle this into a bilinear map `ContinuousLinearMap.holderₗ` and a continuous
bilinear map `ContinuousLinearMap.holderL` under some additional assumptions.

We also declare a heterogeneous scalar multiplication (`HSMul`) instance on `MeasureTheory.Lp`
spaces. Although this could use the `ContinuousLinearMap.holder` construction above, we opt not to
do so in order to minimize the necessary type class assumptions.

When `p q : ℝ≥0∞` are Hölder conjugate (i.e., `HolderConjugate p q`), we also construct the
natural map `ContinuousLinearMap.lpPairing : Lp E p μ →L[𝕜] Lp F q μ →L[𝕜] G` given by
`fun f g ↦ ∫ x, B (f x) (g x) ∂μ`. When `B := (NormedSpace.inclusionInDoubleDual 𝕜 E).flip`, this
is the natural map `Lp (StrongDual 𝕜 E) p μ →L[𝕜] StrongDual 𝕜 (Lp E q μ)`.
-/

open ENNReal MeasureTheory Lp

open scoped NNReal

noncomputable section

/-! ### Induced bilinear maps -/

section Bilinear

variable {α 𝕜 E F G : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {p q r : ENNReal} [hpqr : HolderTriple p q r] [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [NormedSpace 𝕜 G]
    (B : E →L[𝕜] F →L[𝕜] G)

namespace ContinuousLinearMap

variable (r) in

theorem memLp_of_bilin {f : α → E} {g : α → F} (hf : MemLp f p μ) (hg : MemLp g q μ) :
    MemLp (fun x ↦ B (f x) (g x)) r μ :=
  MeasureTheory.MemLp.of_bilin (r := r) (B · ·) ‖B‖₊ hf hg
    (B.aestronglyMeasurable_comp₂ hf.1 hg.1) (.of_forall fun _ ↦ B.le_opNorm₂ _ _)

theorem integrable_of_bilin_of_bdd_left {f : α → E} {g : α → F} (C : ℝ)
    (hf1 : AEStronglyMeasurable f μ) (hf2 : ∀ᵐ a ∂μ, ‖f a‖ ≤ C) (hg : Integrable g μ) :
    Integrable (fun x ↦ B (f x) (g x)) μ :=
  memLp_one_iff_integrable.1 <| B.memLp_of_bilin 1 (memLp_top_of_bound hf1 C hf2)
    (memLp_one_iff_integrable.2 hg)

theorem integrable_of_bilin_of_bdd_right {f : α → E} {g : α → F} (C : ℝ)
    (hf : Integrable f μ) (hg1 : AEStronglyMeasurable g μ) (hg2 : ∀ᵐ a ∂μ, ‖g a‖ ≤ C) :
    Integrable (fun x ↦ B (f x) (g x)) μ :=
  B.flip.integrable_of_bilin_of_bdd_left C hg1 hg2 hf

variable (r) in

def holder (f : Lp E p μ) (g : Lp F q μ) : Lp G r μ :=
  (B.memLp_of_bilin r (Lp.memLp f) (Lp.memLp g)).toLp

lemma coeFn_holder (f : Lp E p μ) (g : Lp F q μ) :
    B.holder r f g =ᵐ[μ] fun x ↦ B (f x) (g x) := by
  rw [holder]
  exact MemLp.coeFn_toLp _

lemma nnnorm_holder_apply_apply_le (f : Lp E p μ) (g : Lp F q μ) :
    ‖B.holder r f g‖₊ ≤ ‖B‖₊ * ‖f‖₊ * ‖g‖₊ := by
  simp_rw [← ENNReal.coe_le_coe, ENNReal.coe_mul, ← enorm_eq_nnnorm, Lp.enorm_def]
  apply eLpNorm_congr_ae (coeFn_holder B f g) |>.trans_le
  exact eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (Lp.memLp f).1 (Lp.memLp g).1 (B · ·) ‖B‖₊
    (.of_forall fun _ ↦ B.le_opNorm₂ _ _)

lemma norm_holder_apply_apply_le (f : Lp E p μ) (g : Lp F q μ) :
    ‖B.holder r f g‖ ≤ ‖B‖ * ‖f‖ * ‖g‖ :=
  NNReal.coe_le_coe.mpr <| nnnorm_holder_apply_apply_le B f g

lemma holder_add_left (f₁ f₂ : Lp E p μ) (g : Lp F q μ) :
    B.holder r (f₁ + f₂) g = B.holder r f₁ g + B.holder r f₂ g := by
  simp only [holder, ← MemLp.toLp_add]
  apply MemLp.toLp_congr
  filter_upwards [AEEqFun.coeFn_add f₁.val f₂.val] with x hx
  simp [hx]

lemma holder_add_right (f : Lp E p μ) (g₁ g₂ : Lp F q μ) :
    B.holder r f (g₁ + g₂) = B.holder r f g₁ + B.holder r f g₂ := by
  simp only [holder, ← MemLp.toLp_add]
  apply MemLp.toLp_congr
  filter_upwards [AEEqFun.coeFn_add g₁.val g₂.val] with x hx
  simp [hx]

lemma holder_smul_left (c : 𝕜) (f : Lp E p μ) (g : Lp F q μ) :
    B.holder r (c • f) g = c • B.holder r f g := by
  simp only [holder, ← MemLp.toLp_const_smul]
  apply MemLp.toLp_congr
  filter_upwards [Lp.coeFn_smul c f] with x hx
  simp [hx]

lemma holder_smul_right (c : 𝕜) (f : Lp E p μ) (g : Lp F q μ) :
    B.holder r f (c • g) = c • B.holder r f g := by
  simp only [holder, ← MemLp.toLp_const_smul]
  apply MemLp.toLp_congr
  filter_upwards [Lp.coeFn_smul c g] with x hx
  simp [hx]

variable (μ p q r) in
