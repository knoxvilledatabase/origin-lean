/-
Extracted from CategoryTheory/Abelian/Projective/Resolution.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Abelian categories with enough projectives have projective resolutions

## Main results
When the underlying category is abelian:
* `CategoryTheory.ProjectiveResolution.lift`: Given `P : ProjectiveResolution X` and
  `Q : ProjectiveResolution Y`, any morphism `X ⟶ Y` admits a lifting to a chain map
  `P.complex ⟶ Q.complex`. It is a lifting in the sense that `P.ι` intertwines the lift and
  the original morphism, see `CategoryTheory.ProjectiveResolution.lift_commutes`.
* `CategoryTheory.ProjectiveResolution.liftHomotopy`: Any two such lifts are homotopic.
* `CategoryTheory.ProjectiveResolution.homotopyEquiv`: Any two projective resolutions of the same
  object are homotopy equivalent.
* `CategoryTheory.projectiveResolutions`: If every object admits a projective resolution, we can
  construct a functor `projectiveResolutions C : C ⥤ HomotopyCategory C (ComplexShape.down ℕ)`.

* `CategoryTheory.exact_d_f`: `Projective.d f` and `f` are exact.
* `CategoryTheory.ProjectiveResolution.of`: Hence, starting from an epimorphism `P ⟶ X`, where `P`
  is projective, we can apply `Projective.d` repeatedly to obtain a projective resolution of `X`.
-/

suppress_compilation

noncomputable section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

open Category Limits Projective

namespace ProjectiveResolution

variable [HasZeroObject C] [HasZeroMorphisms C]

set_option backward.isDefEq.respectTransparency false in

def liftFZero {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q : ProjectiveResolution Z) :
    P.complex.X 0 ⟶ Q.complex.X 0 :=
  Projective.factorThru (P.π.f 0 ≫ f) (Q.π.f 0)

end

section Abelian

variable [Abelian C]

lemma exact₀ {Z : C} (P : ProjectiveResolution Z) :
    (ShortComplex.mk _ _ P.complex_d_comp_π_f_zero).Exact :=
  ShortComplex.exact_of_g_is_cokernel _ P.isColimitCokernelCofork

set_option backward.isDefEq.respectTransparency false in

def liftFOne {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q : ProjectiveResolution Z) :
    P.complex.X 1 ⟶ Q.complex.X 1 :=
  Q.exact₀.liftFromProjective (P.complex.d 1 0 ≫ liftFZero f P Q) (by simp [liftFZero])
