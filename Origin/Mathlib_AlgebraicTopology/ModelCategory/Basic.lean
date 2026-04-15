/-
Extracted from AlgebraicTopology/ModelCategory/Basic.lean
Genuine: 2 of 4 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Model categories

We introduce a typeclass `ModelCategory C` expressing that `C` is equipped with
classes of morphisms named "fibrations", "cofibrations" and "weak equivalences"
which satisfy the axioms of (closed) model categories as they appear for example
in *Simplicial Homotopy Theory* by Goerss and Jardine. We also provide an
alternate constructor `ModelCategory.mk'` which uses a formulation of the axioms
using weak factorization systems.

As a given category `C` may have several model category structures, it is advisable
to define only local instances of `ModelCategory`, or to set these instances on type synonyms.

## References
* [Daniel G. Quillen, Homotopical algebra][Quillen1967]
* [Paul G. Goerss, John F. Jardine, Simplicial Homotopy Theory][goerss-jardine-2009]
* https://ncatlab.org/nlab/show/model+category

-/

universe w v u

namespace HomotopicalAlgebra

open CategoryTheory Limits

variable (C : Type u) [Category.{v} C]

class ModelCategory where
  categoryWithFibrations : CategoryWithFibrations C := by infer_instance
  categoryWithCofibrations : CategoryWithCofibrations C := by infer_instance
  categoryWithWeakEquivalences : CategoryWithWeakEquivalences C := by infer_instance
  cm1a : HasFiniteLimits C := by infer_instance
  cm1b : HasFiniteColimits C := by infer_instance
  cm2 : (weakEquivalences C).HasTwoOutOfThreeProperty := by infer_instance
  cm3a : (weakEquivalences C).IsStableUnderRetracts := by infer_instance
  cm3b : (fibrations C).IsStableUnderRetracts := by infer_instance
  cm3c : (cofibrations C).IsStableUnderRetracts := by infer_instance
  cm4a {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) [Cofibration i] [WeakEquivalence i] [Fibration p] :
      HasLiftingProperty i p := by intros; infer_instance
  cm4b {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) [Cofibration i] [Fibration p] [WeakEquivalence p] :
      HasLiftingProperty i p := by intros; infer_instance
  cm5a : MorphismProperty.HasFactorization (trivialCofibrations C) (fibrations C) := by
    infer_instance
  cm5b : MorphismProperty.HasFactorization (cofibrations C) (trivialFibrations C) := by
    infer_instance

namespace ModelCategory

attribute [instance_reducible]

  categoryWithFibrations categoryWithCofibrations categoryWithWeakEquivalences

attribute [instance] categoryWithFibrations categoryWithCofibrations categoryWithWeakEquivalences

  cm1a cm1b cm2 cm3a cm3b cm3c cm4a cm4b cm5a cm5b

variable [ModelCategory C]

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

end

section mk'

open MorphismProperty

set_option backward.isDefEq.respectTransparency false in

variable {C} in

private lemma mk'.cm3a_aux [CategoryWithFibrations C] [CategoryWithCofibrations C]
    [CategoryWithWeakEquivalences C]
    [(weakEquivalences C).HasTwoOutOfThreeProperty]
    [IsWeakFactorizationSystem (trivialCofibrations C) (fibrations C)]
    [IsWeakFactorizationSystem (cofibrations C) (trivialFibrations C)] {A B X Y : C}
    {f : A ⟶ B} {w : X ⟶ Y} [Fibration f] [WeakEquivalence w]
    (h : RetractArrow f w) : WeakEquivalence f := by
  have hw := factorizationData (trivialCofibrations C) (fibrations C) w
  have : (trivialFibrations C).IsStableUnderRetracts := by
    rw [← cofibrations_rlp]
    infer_instance
  have sq : CommSq h.r.left hw.i f (hw.p ≫ h.r.right) := ⟨by simp⟩
  have hf : fibrations C f := by rwa [← fibration_iff]
  have : HasLiftingProperty hw.i f := hasLiftingProperty_of_wfs _ _ hw.hi hf
  have : RetractArrow f hw.p :=
    { i := Arrow.homMk (h.i.left ≫ hw.i) h.i.right
      r := Arrow.homMk sq.lift h.r.right }
  have h' : trivialFibrations C hw.p :=
    ⟨hw.hp, (weakEquivalence_iff _).1 (weakEquivalence_of_precomp_of_fac hw.fac)⟩
  simpa only [weakEquivalence_iff] using (of_retract this h').2

set_option backward.isDefEq.respectTransparency false in
