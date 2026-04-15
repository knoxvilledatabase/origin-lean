/-
Extracted from Analysis/Fourier/BoundedContinuousFunctionChar.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Definition of BoundedContinuousFunction.char

Definition and basic properties of `BoundedContinuousFunction.char he hL w := fun v ↦ e (L v w)`,
where `e` is a continuous additive character and `L : V →ₗ[ℝ] W →ₗ[ℝ] ℝ` is a continuous bilinear
map.

In the special case `e = Circle.exp`, this is used to define the characteristic function of a
measure.

## Main definitions

- `char he hL w : V →ᵇ ℂ`: Bounded continuous mapping `fun v ↦ e (L v w)` from `V` to `ℂ`, where
  `e` is a continuous additive character and `L : V →ₗ[ℝ] W →ₗ[ℝ] ℝ` is a continuous bilinear map.
- `charPoly he hL : W → ℂ`: The `StarSubalgebra ℂ (V →ᵇ ℂ)` consisting of `ℂ`-linear combinations of
  `char he hL w`, where `w : W`.

## Main statements

- `ext_of_char_eq`: If `e` and `L` are non-trivial, then `char he hL w, w : W` separates
  points in `V`.
- `star_mem_range_charAlgHom`: The family of `ℂ`-linear combinations of `char he hL w, w : W`, is
  closed under `star`.
- `separatesPoints_charPoly`: The family `charPoly he hL w, w : W` separates points in `V`.

-/

open Filter BoundedContinuousFunction Complex

namespace BoundedContinuousFunction

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]
    {e : AddChar ℝ Circle} {L : V →ₗ[ℝ] W →ₗ[ℝ] ℝ}
    {he : Continuous e} {hL : Continuous fun p : V × W ↦ L p.1 p.2}

noncomputable def char (he : Continuous e) (hL : Continuous fun p : V × W ↦ L p.1 p.2)
    (w : W) :
    V →ᵇ ℂ where
  toFun := fun v ↦ e (L v w)
  continuous_toFun :=
    continuous_induced_dom.comp (he.comp (hL.comp (Continuous.prodMk_left w)))
  map_bounded' := by
    refine ⟨2, fun x y ↦ ?_⟩
    calc dist _ _
      ≤ (‖_‖ : ℝ) + ‖_‖ := dist_le_norm_add_norm _ _
    _ ≤ 1 + 1 := add_le_add (by simp) (by simp)
    _ = 2 := by ring
