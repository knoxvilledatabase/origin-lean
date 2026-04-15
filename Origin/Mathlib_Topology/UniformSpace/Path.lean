/-
Extracted from Topology/UniformSpace/Path.lean
Genuine: 7 of 10 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Paths in uniform spaces

In this file we define a `UniformSpace` structure on `Path`s
between two points in a uniform space
and prove that various functions associated with `Path`s are uniformly continuous.

The uniform space structure is induced from the space of continuous maps `C(I, X)`,
and corresponds to uniform convergence of paths on `I`, see `Path.hasBasis_uniformity`.
-/

open scoped unitInterval Topology Uniformity

variable {X : Type*} [UniformSpace X] {x y z : X}

namespace Path

-- INSTANCE (free from Core): instUniformSpace

theorem uniformContinuous (γ : Path x y) : UniformContinuous γ :=
  CompactSpace.uniformContinuous_of_continuous <| map_continuous _

theorem uniformContinuous_extend (γ : Path x y) : UniformContinuous γ.extend :=
  γ.uniformContinuous.comp <| LipschitzWith.projIcc _ |>.uniformContinuous

theorem uniformContinuous_extend_left : UniformContinuous (Path.extend : Path x y → C(ℝ, X)) :=
  ContinuousMap.projIccCM.uniformContinuous_comp_left.comp isUniformEmbedding_coe.uniformContinuous

theorem _root_.Filter.HasBasis.uniformityPath {ι : Sort*} {p : ι → Prop} {U : ι → Set (X × X)}
    (hU : (𝓤 X).HasBasis p U) :
    (𝓤 (Path x y)).HasBasis p fun i ↦ {γ | ∀ t, (γ.1 t, γ.2 t) ∈ U i} :=
  hU.compactConvergenceUniformity_of_compact.comap _

theorem hasBasis_uniformity :
    (𝓤 (Path x y)).HasBasis (· ∈ 𝓤 X) ({γ | ∀ t, (γ.1 t, γ.2 t) ∈ ·}) :=
  (𝓤 X).basis_sets.uniformityPath

theorem uniformContinuous_symm : UniformContinuous (Path.symm : Path x y → Path y x) :=
  hasBasis_uniformity.uniformContinuous_iff hasBasis_uniformity |>.mpr fun U hU ↦
    ⟨U, hU, fun _ _ h x ↦ h (σ x)⟩

theorem uniformContinuous_trans :
    UniformContinuous (Path.trans : Path x y → Path y z → Path x z).uncurry :=
  hasBasis_uniformity.uniformity_prod hasBasis_uniformity
    |>.uniformContinuous_iff hasBasis_uniformity |>.mpr fun U hU ↦
      ⟨(U, U), ⟨hU, hU⟩, fun ⟨_, _⟩ ⟨_, _⟩ ⟨h₁, h₂⟩ t ↦ by
        by_cases ht : (t : ℝ) ≤ 2⁻¹ <;> simp [Path.trans_apply, ht, h₁ _, h₂ _]⟩

-- INSTANCE (free from Core): instCompleteSpace

end Path
