/-
Extracted from Topology/UniformSpace/Matrix.lean
Genuine: 2 of 6 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Uniform space structure on matrices
-/

open Uniformity Topology

variable (m n 𝕜 : Type*) [UniformSpace 𝕜]

namespace Matrix

-- INSTANCE (free from Core): instUniformSpace

-- INSTANCE (free from Core): instIsUniformAddGroup

theorem uniformity :
    𝓤 (Matrix m n 𝕜) = ⨅ (i : m) (j : n), (𝓤 𝕜).comap fun a => (a.1 i j, a.2 i j) := by
  erw [Pi.uniformity]
  simp_rw [Pi.uniformity, Filter.comap_iInf, Filter.comap_comap]
  rfl

theorem uniformContinuous {β : Type*} [UniformSpace β] {f : β → Matrix m n 𝕜} :
    UniformContinuous f ↔ ∀ i j, UniformContinuous fun x => f x i j := by
  simp only [UniformContinuous, Matrix.uniformity, Filter.tendsto_iInf, Filter.tendsto_comap_iff]
  apply Iff.intro <;> intro a <;> apply a

-- INSTANCE (free from Core): [CompleteSpace

-- INSTANCE (free from Core): [T0Space

end Matrix
