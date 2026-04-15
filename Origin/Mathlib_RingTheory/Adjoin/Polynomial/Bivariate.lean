/-
Extracted from RingTheory/Adjoin/Polynomial/Bivariate.lean
Genuine: 3 of 5 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Bivariate polynomials and adjoining transcendental elements

## Main results

* `IsAlgebraic.adjoin_singleton`:
  Given two transcendental elements `a`, `b` over `R`, if one of them, say `a`, is algebraic over
  `R[b]` then `b` is algebraic over `R[a]`.
-/

namespace Polynomial.Bivariate

open Polynomial Bivariate Algebra Transcendental

variable {R A : Type*} [CommRing R]

section Ring

variable [Ring A] [Algebra R A] {x : A}

def Transcendental.algEquivAdjoin (hx : Transcendental R x) :
    R[X][Y] ≃ₐ[R] (Algebra.adjoin R {x})[X] :=
  mapAlgEquiv (algEquivOfTranscendental _ x hx)

attribute [local instance] algebra in

theorem Transcendental.algEquivAdjoin_swap_eq_aeval (hx : Transcendental R x) (p : R[X][Y]) :
    hx.algEquivAdjoin (swap p) = aeval (C ⟨x, self_mem_adjoin_singleton R x⟩) p := by
  simp [algEquivAdjoin, Bivariate.aveal_eq_map_swap]

end Ring

section CommRing

variable [CommRing A] [Algebra R A]

variable {B : Type*} [CommRing B] [Algebra A B] [Algebra R B] [IsScalarTower R A B]

attribute [local instance] Polynomial.algebra in

theorem aeval_aeval_eq_aeval_algEquivAdjoin {x : A} (y : B)
    (hx : Transcendental R x) (p : R[X][Y]) :
    aeval (algebraMap A B x) (aeval (C (⟨y, self_mem_adjoin_singleton R y⟩ :
      adjoin R {y})) p) = aeval y (hx.algEquivAdjoin p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp_all [map_add]
  | monomial n a =>
    simp_all [aeval_algebraMap_apply, Transcendental.algEquivAdjoin, Subalgebra.algebraMap_def]

end CommRing

end Polynomial.Bivariate

end
