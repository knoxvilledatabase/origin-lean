/-
Extracted from Topology/Algebra/Module/Multilinear/Topology.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Topology on continuous multilinear maps

In this file we define `TopologicalSpace` and `UniformSpace` structures
on `ContinuousMultilinearMap 𝕜 E F`,
where `E i` is a family of vector spaces over `𝕜` with topologies
and `F` is a topological vector space.
-/

open Bornology Function Set Topology

open scoped UniformConvergence Filter

namespace ContinuousMultilinearMap

variable {𝕜 ι : Type*} {E : ι → Type*} {F : Type*}
  [NormedField 𝕜]
  [∀ i, TopologicalSpace (E i)] [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)]
  [AddCommGroup F] [Module 𝕜 F]

def toUniformOnFun [TopologicalSpace F] (f : ContinuousMultilinearMap 𝕜 E F) :
    (Π i, E i) →ᵤ[{s | IsVonNBounded 𝕜 s}] F :=
  UniformOnFun.ofFun _ f

open UniformOnFun in

lemma range_toUniformOnFun [DecidableEq ι] [TopologicalSpace F] :
    range toUniformOnFun =
      {f : (Π i, E i) →ᵤ[{s | IsVonNBounded 𝕜 s}] F |
        Continuous (toFun _ f) ∧
        (∀ (m : Π i, E i) i x y,
          toFun _ f (update m i (x + y)) = toFun _ f (update m i x) + toFun _ f (update m i y)) ∧
        (∀ (m : Π i, E i) i (c : 𝕜) x,
          toFun _ f (update m i (c • x)) = c • toFun _ f (update m i x))} := by
  ext f
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨f.cont, f.map_update_add, f.map_update_smul⟩
  · rintro ⟨hcont, hadd, hsmul⟩
    exact ⟨⟨⟨f, by intro; convert hadd, by intro; convert hsmul⟩, hcont⟩, rfl⟩
