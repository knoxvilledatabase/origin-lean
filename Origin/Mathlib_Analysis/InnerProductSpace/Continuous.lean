/-
Extracted from Analysis/InnerProductSpace/Continuous.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Continuity of inner product

We show that the inner product is continuous, `continuous_inner`.

## Tags

inner product space, Hilbert space, norm

-/

noncomputable section

open RCLike Real Filter Topology ComplexConjugate Finsupp

open LinearMap renaming BilinForm → BilinForm

variable {𝕜 E F : Type*} [RCLike 𝕜]

section Continuous

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-!
### Continuity of the inner product
-/

theorem _root_.isBoundedBilinearMap_inner [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] :
    IsBoundedBilinearMap ℝ fun p : E × E => ⟪p.1, p.2⟫ :=
  { add_left := inner_add_left
    smul_left := fun r x y => by
      simp only [← algebraMap_smul 𝕜 r x, algebraMap_eq_ofReal, inner_smul_real_left]
    add_right := inner_add_right
    smul_right := fun r x y => by
      simp only [← algebraMap_smul 𝕜 r y, algebraMap_eq_ofReal, inner_smul_real_right]
    bound :=
      ⟨1, zero_lt_one, fun x y => by
        rw [one_mul]
        exact norm_inner_le_norm x y⟩ }

theorem continuous_inner : Continuous fun p : E × E => ⟪p.1, p.2⟫ :=
  letI : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal 𝕜 E
  haveI := IsScalarTower.restrictScalars ℝ 𝕜 E
  isBoundedBilinearMap_inner.continuous

variable {α : Type*}

theorem Filter.Tendsto.inner {f g : α → E} {l : Filter α} {x y : E} (hf : Tendsto f l (𝓝 x))
    (hg : Tendsto g l (𝓝 y)) : Tendsto (fun t => ⟪f t, g t⟫) l (𝓝 ⟪x, y⟫) :=
  (continuous_inner.tendsto _).comp (hf.prodMk_nhds hg)

variable [TopologicalSpace α] {f g : α → E} {x : α} {s : Set α}

theorem ContinuousWithinAt.inner (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x) :
    ContinuousWithinAt (fun t => ⟪f t, g t⟫) s x :=
  Filter.Tendsto.inner hf hg
