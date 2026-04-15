/-
Extracted from Topology/Algebra/Module/FiniteDimensionBilinear.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Building continuous bilinear maps in finite dimensions over complete fields

Given a complete nontrivially normed field `𝕜` and finite dimensional T₂ topological vector spaces
over `𝕜`, this file builds a continuous bilinear map from any bilinear function.

This applies in particular to evaluation of linear maps between such spaces.

Working with topological vector spaces instead of normed spaces is important for applications in the
differential geometry part of Mathlib where we don’t want to fix a norm on tangent spaces for
instance.

-/

variable
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E] [T2Space E]
    {F : Type*} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F] [FiniteDimensional 𝕜 F] [T2Space F]
    {G : Type*} [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [ContinuousSMul 𝕜 G]

def LinearMap.toContinuousBilinearMap (f : E →ₗ[𝕜] F →ₗ[𝕜] G) : E →L[𝕜] F →L[𝕜] G :=
  IsLinearMap.mk' (fun x : E ↦ f x |>.toContinuousLinearMap)
      (by constructor <;> (intros; simp)) |>.toContinuousLinearMap
