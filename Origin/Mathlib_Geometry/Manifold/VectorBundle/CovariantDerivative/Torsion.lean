/-
Extracted from Geometry/Manifold/VectorBundle/CovariantDerivative/Torsion.lean
Genuine: 6 of 6 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Torsion of an affine connection

We define the torsion tensor of an affine connection, i.e. a covariant derivative on the tangent
bundle `TM` of some manifold `M`.

## Main definitions and results

* `IsCovariantDerivativeOn.torsion`: the torsion tensor of an unbundled covariant derivative
  on `TM`
* `CovariantDerivative.torsion`: the torsion tensor of a bundled covariant derivative on `TM`
* `CovariantDerivative.torsion_eq_zero_iff`: the torsion tensor of a bundled covariant derivative
  `∇` vanishes if and only if `∇_X Y - ∇_Y X = [X, Y]` for all differentiable vector fields
  `X` and `Y`.

-/

public noncomputable section

open Bundle Set NormedSpace FiberBundle

open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {x : M}

/-! ## Torsion tensor of an unbundled covariant derivative on `TM` on a set `s` -/

namespace IsCovariantDerivativeOn

private def torsionAux
    (cov : (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x →L[𝕜] TangentSpace I x)) :
    (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x) :=
  fun X Y x ↦ cov Y x (X x) - cov X x (Y x) - VectorField.mlieBracket I X Y x

variable [IsManifold I 2 M] [CompleteSpace E]
  {cov cov' : (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x →L[𝕜] TangentSpace I x)}
  {X X' Y : Π x : M, TangentSpace I x}

private theorem torsionAux_tensorial₁ (hcov : IsCovariantDerivativeOn E cov) (x : M)
    (Y : Π x, TangentSpace I x) :
    TensorialAt I E (torsionAux cov · Y x) x where
  smul hf hX := by
    simp [torsionAux, hcov.leibniz hX hf, VectorField.mlieBracket_smul_left hf hX]
    module
  add hX hX' := by
    simp [torsionAux, hcov.add hX hX', VectorField.mlieBracket_add_left hX hX']
    module

private theorem torsionAux_tensorial₂ (hcov : IsCovariantDerivativeOn E cov) (x : M)
    (X : Π x, TangentSpace I x) :
    TensorialAt I E (torsionAux cov X · x) x where
  smul hf hY := by
    simp [torsionAux, hcov.leibniz hY hf, VectorField.mlieBracket_smul_right hf hY]
    module
  add hY hY' := by
    simp [torsionAux, hcov.add hY hY', VectorField.mlieBracket_add_right hY hY']
    module

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]

noncomputable def torsion (hcov : IsCovariantDerivativeOn E cov univ) (x : M) :
    TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] TangentSpace I x :=
  TensorialAt.mkHom₂ (torsionAux cov · · x) _
    (fun τ _ ↦ hcov.torsionAux_tensorial₁ x τ)
    (fun σ _ ↦ hcov.torsionAux_tensorial₂ x σ)

theorem torsion_apply (hcov : IsCovariantDerivativeOn E cov univ) {x}
    {X : Π x : M, TangentSpace I x} (hX : MDiffAt (T% X) x)
    {Y : Π x : M, TangentSpace I x} (hY : MDiffAt (T% Y) x) :
    torsion hcov x (X x) (Y x) = cov Y x (X x) - cov X x (Y x) - VectorField.mlieBracket I X Y x :=
  TensorialAt.mkHom₂_apply _ _ hX hY

theorem torsion_apply_eq_extend (hcov : IsCovariantDerivativeOn E cov univ) {x}
    (X₀ Y₀ : TangentSpace I x) :
    torsion hcov x X₀ Y₀ =
      cov (extend E Y₀) x X₀ - cov (extend E X₀) x Y₀ -
        VectorField.mlieBracket I (extend E X₀) (extend E Y₀) x := by
  simp [torsion, torsionAux, TensorialAt.mkHom₂_apply_eq_extend]

variable (X) in
