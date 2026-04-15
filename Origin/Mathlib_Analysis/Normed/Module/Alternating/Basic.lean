/-
Extracted from Analysis/Normed/Module/Alternating/Basic.lean
Genuine: 8 of 9 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Operator norm on the space of continuous alternating maps

In this file we show that continuous alternating maps
from a seminormed space to a (semi)normed space form a (semi)normed space.
We also prove basic facts about this norm
and define bundled versions of some operations on continuous alternating maps.

Most proofs just invoke the corresponding fact about continuous multilinear maps.
-/

noncomputable section

open scoped NNReal

open Finset Metric

/-!
### Type variables

We use the following type variables in this file:

* `𝕜` : a nontrivially normed field;
* `ι`: a finite index type;
* `E`, `F`, `G`: (semi)normed vector spaces over `𝕜`.
-/

-- INSTANCE (free from Core): ContinuousAlternatingMap.instContinuousEval

section Seminorm

universe u wE wF wG v

variable {𝕜 : Type u} {n : ℕ} {E : Type wE} {F : Type wF} {G : Type wG} {ι : Type v}
  [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]

/-!
### Continuity properties of alternating maps

We relate continuity of alternating maps to the inequality `‖f m‖ ≤ C * ∏ i, ‖m i‖`, in
both directions. Along the way, we prove useful bounds on the difference `‖f m₁ - f m₂‖`.
-/

namespace AlternatingMap

theorem norm_map_coord_zero (f : E [⋀^ι]→ₗ[𝕜] F) (hf : Continuous f)
    {m : ι → E} {i : ι} (hi : ‖m i‖ = 0) : ‖f m‖ = 0 :=
  f.1.norm_map_coord_zero hf hi

variable [Fintype ι]

theorem bound_of_shell_of_norm_map_coord_zero (f : E [⋀^ι]→ₗ[𝕜] F)
    (hf₀ : ∀ {m i}, ‖m i‖ = 0 → ‖f m‖ = 0)
    {ε : ι → ℝ} {C : ℝ} (hε : ∀ i, 0 < ε i) {c : ι → 𝕜} (hc : ∀ i, 1 < ‖c i‖)
    (hf : ∀ m : ι → E, (∀ i, ε i / ‖c i‖ ≤ ‖m i‖) → (∀ i, ‖m i‖ < ε i) → ‖f m‖ ≤ C * ∏ i, ‖m i‖)
    (m : ι → E) : ‖f m‖ ≤ C * ∏ i, ‖m i‖ :=
  f.1.bound_of_shell_of_norm_map_coord_zero hf₀ hε hc hf m

theorem bound_of_shell_of_continuous (f : E [⋀^ι]→ₗ[𝕜] F) (hfc : Continuous f)
    {ε : ℝ} {C : ℝ} (hε : 0 < ε) {c : 𝕜} (hc : 1 < ‖c‖)
    (hf : ∀ m : ι → E, (∀ i, ε / ‖c‖ ≤ ‖m i‖) → (∀ i, ‖m i‖ < ε) → ‖f m‖ ≤ C * ∏ i, ‖m i‖)
    (m : ι → E) : ‖f m‖ ≤ C * ∏ i, ‖m i‖ :=
  f.1.bound_of_shell_of_continuous hfc (fun _ ↦ hε) (fun _ ↦ hc) hf m

theorem exists_bound_of_continuous (f : E [⋀^ι]→ₗ[𝕜] F) (hf : Continuous f) :
    ∃ (C : ℝ), 0 < C ∧ (∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖) :=
  f.1.exists_bound_of_continuous hf

theorem norm_image_sub_le_of_bound' [DecidableEq ι] (f : E [⋀^ι]→ₗ[𝕜] F) {C : ℝ} (hC : 0 ≤ C)
    (H : ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖) (m₁ m₂ : ι → E) :
    ‖f m₁ - f m₂‖ ≤ C * ∑ i, ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖ :=
  f.toMultilinearMap.norm_image_sub_le_of_bound' hC H m₁ m₂

theorem norm_image_sub_le_of_bound (f : E [⋀^ι]→ₗ[𝕜] F) {C : ℝ} (hC : 0 ≤ C)
    (H : ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖) (m₁ m₂ : ι → E) :
    ‖f m₁ - f m₂‖ ≤ C * (Fintype.card ι) * (max ‖m₁‖ ‖m₂‖) ^ (Fintype.card ι - 1) * ‖m₁ - m₂‖ :=
  f.toMultilinearMap.norm_image_sub_le_of_bound hC H m₁ m₂

theorem continuous_of_bound (f : E [⋀^ι]→ₗ[𝕜] F) (C : ℝ) (H : ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖) :
    Continuous f :=
  f.toMultilinearMap.continuous_of_bound C H

def mkContinuous (f : E [⋀^ι]→ₗ[𝕜] F) (C : ℝ) (H : ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖) : E [⋀^ι]→L[𝕜] F :=
  { f with cont := f.continuous_of_bound C H }
