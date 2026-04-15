/-
Extracted from CategoryTheory/Monoidal/Closed/Ideal.lean
Genuine: 6 of 9 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Exponential ideals

An exponential ideal of a Cartesian closed category `C` is a subcategory `D ⊆ C` such that for any
`B : D` and `A : C`, the exponential `A ⟹ B` is in `D`: resembling ring-theoretic ideals. We
define the notion here for inclusion functors `i : D ⥤ C` rather than explicit subcategories to
preserve the principle of equivalence.

We additionally show that if `C` is Cartesian closed and `i : D ⥤ C` is a reflective functor, the
following are equivalent.
* The left adjoint to `i` preserves binary (equivalently, finite) products.
* `i` is an exponential ideal.
-/

universe v₁ v₂ u₁ u₂

noncomputable section

namespace CategoryTheory

open Category

open scoped CartesianClosed

section Ideal

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₁} D] {i : D ⥤ C}

variable (i) [CartesianMonoidalCategory C] [MonoidalClosed C]

class ExponentialIdeal : Prop where
  exp_closed : ∀ {B}, i.essImage B → ∀ A, i.essImage (A ⟹ B)

attribute [nolint docBlame] ExponentialIdeal.exp_closed

theorem ExponentialIdeal.mk' (h : ∀ (B : D) (A : C), i.essImage (A ⟹ i.obj B)) :
    ExponentialIdeal i :=
  ⟨fun hB A => by
    rcases hB with ⟨B', ⟨iB'⟩⟩
    exact Functor.essImage.ofIso ((ihom A).mapIso iB') (h B' A)⟩

-- INSTANCE (free from Core): :

open MonoidalClosed

-- INSTANCE (free from Core): :

set_option backward.isDefEq.respectTransparency false in

def exponentialIdealReflective (A : C) [Reflective i] [ExponentialIdeal i] :
    i ⋙ ihom A ⋙ reflector i ⋙ i ≅ i ⋙ ihom A := by
  symm
  apply NatIso.ofComponents _ _
  · intro X
    haveI := Functor.essImage.unit_isIso (ExponentialIdeal.exp_closed (i.obj_mem_essImage X) A)
    apply asIso ((reflectorAdjunction i).unit.app (A ⟹ i.obj X))
  · simp [asIso]

theorem ExponentialIdeal.mk_of_iso [Reflective i]
    (h : ∀ A : C, i ⋙ ihom A ⋙ reflector i ⋙ i ≅ i ⋙ ihom A) : ExponentialIdeal i := by
  apply ExponentialIdeal.mk'
  intro B A
  exact ⟨_, ⟨(h A).app B⟩⟩

end Ideal

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₁} D]

variable (i : D ⥤ C)

theorem reflective_products [Limits.HasFiniteProducts C] [Reflective i] :
    Limits.HasFiniteProducts D := ⟨fun _ => hasLimitsOfShape_of_reflective i⟩

open MonoidalClosed MonoidalCategory CartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false in

open Limits in

abbrev CartesianMonoidalCategory.ofReflective [CartesianMonoidalCategory C] [Reflective i] :
    CartesianMonoidalCategory D :=
  .ofChosenFiniteProducts
    ({ cone := Limits.asEmptyCone <| (reflector i).obj (𝟙_ C)
       isLimit := by
         apply isLimitOfReflects i
         apply isLimitChangeEmptyCone _ isTerminalTensorUnit
         letI : IsIso ((reflectorAdjunction i).unit.app (𝟙_ C)) := by
           have := reflective_products i
           refine Functor.essImage.unit_isIso ⟨terminal D, ⟨PreservesTerminal.iso i |>.trans ?_⟩⟩
           exact IsLimit.conePointUniqueUpToIso (limit.isLimit _) isTerminalTensorUnit
         exact asIso ((reflectorAdjunction i).unit.app (𝟙_ C)) })
  fun X Y ↦
    { cone := BinaryFan.mk
        ((reflector i).map (fst (i.obj X) (i.obj Y)) ≫ (reflectorAdjunction i).counit.app _)
        ((reflector i).map (snd (i.obj X) (i.obj Y)) ≫ (reflectorAdjunction i).counit.app _)
      isLimit := by
        apply isLimitOfReflects i
        apply IsLimit.equivOfNatIsoOfIso (pairComp X Y _) _ _ _ |>.invFun
          (tensorProductIsBinaryProduct (i.obj X) (i.obj Y))
        fapply BinaryFan.ext
        · change (reflector i ⋙ i).obj (i.obj X ⊗ i.obj Y) ≅ (𝟭 C).obj (i.obj X ⊗ i.obj Y)
          letI : IsIso ((reflectorAdjunction i).unit.app (i.obj X ⊗ i.obj Y)) := by
            apply Functor.essImage.unit_isIso
            haveI := reflective_products i
            use Limits.prod X Y
            constructor
            apply Limits.PreservesLimitPair.iso i _ _ |>.trans
            refine Limits.IsLimit.conePointUniqueUpToIso (limit.isLimit (pair (i.obj X) (i.obj Y)))
              (tensorProductIsBinaryProduct _ _)
          exact asIso ((reflectorAdjunction i).unit.app (i.obj X ⊗ i.obj Y)) |>.symm
        · simp only [BinaryFan.fst, Cone.postcompose, pairComp]
          simp [← Functor.comp_map, ← NatTrans.naturality_assoc]
        · simp only [BinaryFan.snd, Cone.postcompose, pairComp]
          simp [← Functor.comp_map, ← NatTrans.naturality_assoc] }

variable [CartesianMonoidalCategory C] [Reflective i] [MonoidalClosed C]
  [CartesianMonoidalCategory D]

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): (priority

variable [ExponentialIdeal i]
