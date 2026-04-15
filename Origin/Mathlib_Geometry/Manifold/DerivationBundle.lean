/-
Extracted from Geometry/Manifold/DerivationBundle.lean
Genuine: 7 | Conflates: 0 | Dissolved: 0 | Infrastructure: 15
-/
import Origin.Core
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
import Mathlib.RingTheory.Derivation.Basic

/-!

# Derivation bundle

In this file we define the derivations at a point of a manifold on the algebra of smooth functions.
Moreover, we define the differential of a function in terms of derivations.

The content of this file is not meant to be regarded as an alternative definition to the current
tangent bundle but rather as a purely algebraic theory that provides a purely algebraic definition
of the Lie algebra for a Lie group.

-/

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) (M : Type*)
  [TopologicalSpace M] [ChartedSpace H M] (n : ℕ∞)

open scoped Manifold

local notation "∞" => (⊤ : ℕ∞)

instance smoothFunctionsAlgebra : Algebra 𝕜 C^∞⟮I, M; 𝕜⟯ := by infer_instance

instance smooth_functions_tower : IsScalarTower 𝕜 C^∞⟮I, M; 𝕜⟯ C^∞⟮I, M; 𝕜⟯ := by infer_instance

@[nolint unusedArguments]
def PointedSmoothMap (_ : M) :=
  C^n⟮I, M; 𝕜⟯

scoped[Derivation] notation "C^" n "⟮" I ", " M "; " 𝕜 "⟯⟨" x "⟩" => PointedSmoothMap 𝕜 I M n x

variable {𝕜 M}

namespace PointedSmoothMap

open scoped Derivation

instance instFunLike {x : M} : FunLike C^∞⟮I, M; 𝕜⟯⟨x⟩ M 𝕜 :=
  ContMDiffMap.instFunLike

instance {x : M} : CommRing C^∞⟮I, M; 𝕜⟯⟨x⟩ :=
  SmoothMap.commRing

instance {x : M} : Algebra 𝕜 C^∞⟮I, M; 𝕜⟯⟨x⟩ :=
  SmoothMap.algebra

instance {x : M} : Inhabited C^∞⟮I, M; 𝕜⟯⟨x⟩ :=
  ⟨0⟩

instance {x : M} : Algebra C^∞⟮I, M; 𝕜⟯⟨x⟩ C^∞⟮I, M; 𝕜⟯ :=
  Algebra.id C^∞⟮I, M; 𝕜⟯

instance {x : M} : IsScalarTower 𝕜 C^∞⟮I, M; 𝕜⟯⟨x⟩ C^∞⟮I, M; 𝕜⟯ :=
  IsScalarTower.right

variable {I}

instance evalAlgebra {x : M} : Algebra C^∞⟮I, M; 𝕜⟯⟨x⟩ 𝕜 :=
  (SmoothMap.evalRingHom x : C^∞⟮I, M; 𝕜⟯⟨x⟩ →+* 𝕜).toAlgebra

def eval (x : M) : C^∞⟮I, M; 𝕜⟯ →ₐ[C^∞⟮I, M; 𝕜⟯⟨x⟩] 𝕜 :=
  Algebra.ofId C^∞⟮I, M; 𝕜⟯⟨x⟩ 𝕜

theorem smul_def (x : M) (f : C^∞⟮I, M; 𝕜⟯⟨x⟩) (k : 𝕜) : f • k = f x * k :=
  rfl

instance (x : M) : IsScalarTower 𝕜 C^∞⟮I, M; 𝕜⟯⟨x⟩ 𝕜 where
  smul_assoc k f h := by
    rw [smul_def, smul_def, SmoothMap.coe_smul, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_assoc]

end PointedSmoothMap

open scoped Derivation

abbrev PointDerivation (x : M) :=
  Derivation 𝕜 C^∞⟮I, M; 𝕜⟯⟨x⟩ 𝕜

section

open scoped Derivation

variable (X : Derivation 𝕜 C^∞⟮I, M; 𝕜⟯ C^∞⟮I, M; 𝕜⟯) (f : C^∞⟮I, M; 𝕜⟯)

def SmoothFunction.evalAt (x : M) : C^∞⟮I, M; 𝕜⟯ →ₗ[C^∞⟮I, M; 𝕜⟯⟨x⟩] 𝕜 :=
  (PointedSmoothMap.eval x).toLinearMap

namespace Derivation

variable {I}

def evalAt (x : M) : Derivation 𝕜 C^∞⟮I, M; 𝕜⟯ C^∞⟮I, M; 𝕜⟯ →ₗ[𝕜] PointDerivation I x :=
  (SmoothFunction.evalAt I x).compDer

theorem evalAt_apply (x : M) : evalAt x X f = (X f) x :=
  rfl

end Derivation

variable {I} {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*}
  [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*} [TopologicalSpace M']
  [ChartedSpace H' M']

def hfdifferential {f : C^∞⟮I, M; I', M'⟯} {x : M} {y : M'} (h : f x = y) :
    PointDerivation I x →ₗ[𝕜] PointDerivation I' y where
  toFun v :=
    Derivation.mk'
      { toFun := fun g => v (g.comp f)
        map_add' := fun g g' => by dsimp; rw [SmoothMap.add_comp, Derivation.map_add]
        map_smul' := fun k g => by
          dsimp; rw [SmoothMap.smul_comp, Derivation.map_smul, smul_eq_mul] }
      fun g g' => by
        dsimp
        rw [SmoothMap.mul_comp, Derivation.leibniz,
          PointedSmoothMap.smul_def, ContMDiffMap.comp_apply,
          PointedSmoothMap.smul_def, ContMDiffMap.comp_apply, h]
        norm_cast
  map_smul' _ _ := rfl
  map_add' _ _ := rfl

def fdifferential (f : C^∞⟮I, M; I', M'⟯) (x : M) :
    PointDerivation I x →ₗ[𝕜] PointDerivation I' (f x) :=
  hfdifferential (rfl : f x = f x)

scoped[Manifold] notation "𝒅" => fdifferential

scoped[Manifold] notation "𝒅ₕ" => hfdifferential

@[simp]
theorem fdifferential_apply (f : C^∞⟮I, M; I', M'⟯) {x : M} (v : PointDerivation I x)
    (g : C^∞⟮I', M'; 𝕜⟯) : 𝒅 f x v g = v (g.comp f) :=
  rfl

@[simp]
theorem hfdifferential_apply {f : C^∞⟮I, M; I', M'⟯} {x : M} {y : M'} (h : f x = y)
    (v : PointDerivation I x) (g : C^∞⟮I', M'; 𝕜⟯) : 𝒅ₕ h v g = 𝒅 f x v g :=
  rfl

variable {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] {H'' : Type*}
  [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''} {M'' : Type*} [TopologicalSpace M'']
  [ChartedSpace H'' M'']

@[simp]
theorem fdifferential_comp (g : C^∞⟮I', M'; I'', M''⟯) (f : C^∞⟮I, M; I', M'⟯) (x : M) :
    𝒅 (g.comp f) x = (𝒅 g (f x)).comp (𝒅 f x) :=
  rfl

end
