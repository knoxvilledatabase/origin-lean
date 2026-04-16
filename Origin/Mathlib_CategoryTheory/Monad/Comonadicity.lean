/-
Extracted from CategoryTheory/Monad/Comonadicity.lean
Genuine: 21 | Conflates: 0 | Dissolved: 0 | Infrastructure: 12
-/
import Origin.Core
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.Reflexive
import Mathlib.CategoryTheory.Monad.Equalizer
import Mathlib.CategoryTheory.Monad.Limits

noncomputable section

/-!
# Comonadicity theorems

We prove comonadicity theorems which can establish a given functor is comonadic. In particular, we
show three versions of Beck's comonadicity theorem, and the coreflexive (crude)
comonadicity theorem:

`F` is a comonadic left adjoint if it has a right adjoint, and:

* `C` has, `F` preserves and reflects `F`-split equalizers, see
  `CategoryTheory.Monad.comonadicOfHasPreservesReflectsFSplitEqualizers`
* `F` creates `F`-split coequalizers, see
  `CategoryTheory.Monad.comonadicOfCreatesFSplitEqualizers`
  (The converse of this is also shown, see
   `CategoryTheory.Monad.createsFSplitEqualizersOfComonadic`)
* `C` has and `F` preserves `F`-split equalizers, and `F` reflects isomorphisms, see
  `CategoryTheory.Monad.comonadicOfHasPreservesFSplitEqualizersOfReflectsIsomorphisms`
* `C` has and `F` preserves coreflexive equalizers, and `F` reflects isomorphisms, see
  `CategoryTheory.Monad.comonadicOfHasPreservesCoreflexiveEqualizersOfReflectsIsomorphisms`

This file has been adapted from `Mathlib.CategoryTheory.Monad.Monadicity`.
Please try to keep them in sync.

## Tags

Beck, comonadicity, descent

-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Comonad

open Limits

noncomputable section

namespace ComonadicityInternal

variable {C : Type u₁} {D : Type u₂}

variable [Category.{v₁} C] [Category.{v₁} D]

variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

instance main_pair_coreflexive (A : adj.toComonad.Coalgebra) :
    IsCoreflexivePair (G.map A.a) (adj.unit.app (G.obj A.A)) := by
  apply IsCoreflexivePair.mk' (G.map (adj.counit.app _)) _ _
  · rw [← G.map_comp, ← G.map_id]
    exact congr_arg G.map A.counit
  · rw [adj.right_triangle_components]
    rfl

instance main_pair_F_cosplit (A : adj.toComonad.Coalgebra) :
    F.IsCosplitPair (G.map A.a)
      (adj.unit.app (G.obj A.A)) where
  splittable := ⟨_, _, ⟨beckSplitEqualizer A⟩⟩

def comparisonRightAdjointObj (A : adj.toComonad.Coalgebra)
    [HasEqualizer (G.map A.a) (adj.unit.app _)] : C :=
  equalizer (G.map A.a) (adj.unit.app _)

@[simps!]
def comparisonRightAdjointHomEquiv (A : adj.toComonad.Coalgebra) (B : C)
    [HasEqualizer (G.map A.a) (adj.unit.app (G.obj A.A))] :
    ((comparison adj).obj B ⟶ A) ≃ (B ⟶ comparisonRightAdjointObj adj A) where
      toFun f := by
        refine equalizer.lift (adj.homEquiv _ _ f.f) ?_
        simp only [Adjunction.toComonad_coe, Functor.comp_obj, Adjunction.homEquiv_unit,
          Functor.id_obj, Category.assoc, ← G.map_comp, ← f.h, comparison_obj_A, comparison_obj_a]
        rw [Functor.comp_map, Functor.map_comp, Adjunction.unit_naturality_assoc,
          Adjunction.unit_naturality]
      invFun f := by
        refine ⟨(adj.homEquiv _ _).symm (f ≫ (equalizer.ι _ _)), (adj.homEquiv _ _).injective ?_⟩
        simp only [Adjunction.toComonad_coe, Functor.comp_obj, comparison_obj_A, comparison_obj_a,
          Adjunction.homEquiv_counit, Functor.id_obj, Functor.map_comp, Category.assoc,
          Functor.comp_map, Adjunction.homEquiv_unit, Adjunction.unit_naturality_assoc,
          Adjunction.unit_naturality, Adjunction.right_triangle_components_assoc]
        congr 1
        exact (equalizer.condition _ _).symm
      left_inv f := by aesop
      right_inv f := by apply equalizer.hom_ext; simp

def rightAdjointComparison
    [∀ A : adj.toComonad.Coalgebra, HasEqualizer (G.map A.a)
      (adj.unit.app (G.obj A.A))] :
    adj.toComonad.Coalgebra ⥤ C := by
  refine
    Adjunction.rightAdjointOfEquiv (F := comparison adj)
      (G_obj := fun A => comparisonRightAdjointObj adj A) (fun A B => ?_) ?_
  · apply comparisonRightAdjointHomEquiv
  · intro A B B' g h
    apply equalizer.hom_ext
    simp [Adjunction.homEquiv_unit]

@[simps! counit]
def comparisonAdjunction
    [∀ A : adj.toComonad.Coalgebra, HasEqualizer (G.map A.a)
      (adj.unit.app (G.obj A.A))] :
    comparison adj ⊣ rightAdjointComparison adj :=
  Adjunction.adjunctionOfEquivRight _ _

variable {adj}

theorem comparisonAdjunction_counit_f_aux
    [∀ A : adj.toComonad.Coalgebra, HasEqualizer (G.map A.a)
      (adj.unit.app (G.obj A.A))]
    (A : adj.toComonad.Coalgebra) :
    ((comparisonAdjunction adj).counit.app A).f =
      (adj.homEquiv _ A.A).symm (equalizer.ι (G.map A.a) (adj.unit.app (G.obj A.A))) :=
  congr_arg (adj.homEquiv _ _).symm (Category.id_comp _)

@[simps! pt]
def counitFork (A : adj.toComonad.Coalgebra)
    [HasEqualizer (G.map A.a) (adj.unit.app (G.obj A.A))] :
    Fork (F.map (G.map A.a)) (F.map (adj.unit.app (G.obj A.A))) :=
  Fork.ofι (F.map (equalizer.ι (G.map A.a) (adj.unit.app (G.obj A.A))))
    (by
      change _ = F.map _ ≫ _
      rw [← F.map_comp, equalizer.condition, F.map_comp])

theorem comparisonAdjunction_counit_f
    [∀ A : adj.toComonad.Coalgebra, HasEqualizer (G.map A.a)
      (adj.unit.app (G.obj A.A))]
    (A : adj.toComonad.Coalgebra) :
    ((comparisonAdjunction adj).counit.app A).f = (beckEqualizer A).lift (counitFork A) := by
  simp [Adjunction.homEquiv_counit]

variable (adj)

@[simps!]
def unitFork (B : C) :
    Fork (G.map (F.map (adj.unit.app B)))
      (adj.unit.app (G.obj (F.obj B))) :=
  Fork.ofι (adj.unit.app B) (adj.unit_naturality _)

variable {adj} in

def counitLimitOfPreservesEqualizer (A : adj.toComonad.Coalgebra)
    [HasEqualizer (G.map A.a) (adj.unit.app (G.obj A.A))]
    [PreservesLimit (parallelPair (G.map A.a) (adj.unit.app (G.obj A.A))) F] :
    IsLimit (counitFork (G := G) A) :=
  isLimitOfHasEqualizerOfPreservesLimit F _ _

def unitEqualizerOfCoreflectsEqualizer (B : C)
    [ReflectsLimit (parallelPair (G.map (F.map (adj.unit.app B)))
      (adj.unit.app (G.obj (F.obj B)))) F] :
    IsLimit (unitFork (adj := adj) B) :=
  isLimitOfIsLimitForkMap F _ (beckEqualizer ((comparison adj).obj B))

instance

    [∀ A : adj.toComonad.Coalgebra, HasEqualizer (G.map A.a) (adj.unit.app (G.obj A.A))]

    (B : C) : HasLimit (parallelPair

      (G.map (F.map (NatTrans.app adj.unit B)))

      (NatTrans.app adj.unit (G.obj (F.obj B)))) :=

  inferInstanceAs <| HasEqualizer

    (G.map ((comparison adj).obj B).a)

    (adj.unit.app (G.obj ((comparison adj).obj B).A))

theorem comparisonAdjunction_unit_app
    [∀ A : adj.toComonad.Coalgebra, HasEqualizer (G.map A.a) (adj.unit.app (G.obj A.A))] (B : C) :
    (comparisonAdjunction adj).unit.app B = limit.lift _ (unitFork adj B) := by
  apply equalizer.hom_ext
  change
    equalizer.lift ((adj.homEquiv B _) (𝟙 _)) _ ≫ equalizer.ι _ _ =
      equalizer.lift _ _ ≫ equalizer.ι _ _
  simp [Adjunction.homEquiv_unit]

end ComonadicityInternal

open CategoryTheory Adjunction Comonad ComonadicityInternal

variable {C : Type u₁} {D : Type u₂}

variable [Category.{v₁} C] [Category.{v₁} D]

variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

variable (G) in

def createsFSplitEqualizersOfComonadic [ComonadicLeftAdjoint F] ⦃A B⦄ (f g : A ⟶ B)
    [F.IsCosplitPair f g] : CreatesLimit (parallelPair f g) F := by
  apply (config := {allowSynthFailures := true}) comonadicCreatesLimitOfPreservesLimit
  all_goals
    apply @preservesLimit_of_iso_diagram _ _ _ _ _ _ _ _ _ (diagramIsoParallelPair.{v₁} _).symm ?_
    dsimp
    infer_instance

section BeckComonadicity

class HasEqualizerOfIsCosplitPair (F : C ⥤ D) : Prop where
  /-- If `f, g` is an `F`-cosplit pair, then they have an equalizer. -/
  out : ∀ {A B} (f g : A ⟶ B) [F.IsCosplitPair f g], HasEqualizer f g

instance [HasEqualizerOfIsCosplitPair F] : ∀ (A : Coalgebra adj.toComonad),
    HasEqualizer (G.map A.a)
      (adj.unit.app (G.obj A.A)) :=
  fun _ => HasEqualizerOfIsCosplitPair.out F _ _

class PreservesLimitOfIsCosplitPair (F : C ⥤ D) where
  /-- If `f, g` is an `F`-cosplit pair, then `F` preserves limits of `parallelPair f g`. -/
  out : ∀ {A B} (f g : A ⟶ B) [F.IsCosplitPair f g], PreservesLimit (parallelPair f g) F

instance {A B} (f g : A ⟶ B) [F.IsCosplitPair f g] [PreservesLimitOfIsCosplitPair F] :
    PreservesLimit (parallelPair f g) F := PreservesLimitOfIsCosplitPair.out f g

instance [PreservesLimitOfIsCosplitPair F] : ∀ (A : Coalgebra adj.toComonad),
   PreservesLimit (parallelPair (G.map A.a)
      (NatTrans.app adj.unit (G.obj A.A))) F :=
  fun _ => PreservesLimitOfIsCosplitPair.out _ _

class ReflectsLimitOfIsCosplitPair (F : C ⥤ D) where
  /-- If `f, g` is an `F`-cosplit pair, then `F` reflects limits for `parallelPair f g`. -/
  out : ∀ {A B} (f g : A ⟶ B) [F.IsCosplitPair f g], ReflectsLimit (parallelPair f g) F

instance {A B} (f g : A ⟶ B) [F.IsCosplitPair f g] [ReflectsLimitOfIsCosplitPair F] :
    ReflectsLimit (parallelPair f g) F := ReflectsLimitOfIsCosplitPair.out f g

instance [ReflectsLimitOfIsCosplitPair F] : ∀ (A : Coalgebra adj.toComonad),
    ReflectsLimit (parallelPair (G.map A.a)
      (NatTrans.app adj.unit (G.obj A.A))) F :=
  fun _ => ReflectsLimitOfIsCosplitPair.out _ _

def comonadicOfHasPreservesReflectsFSplitEqualizers [HasEqualizerOfIsCosplitPair F]
    [PreservesLimitOfIsCosplitPair F] [ReflectsLimitOfIsCosplitPair F] :
    ComonadicLeftAdjoint F where
  adj := adj
  eqv := by
    have : ∀ (X : Coalgebra adj.toComonad), IsIso ((comparisonAdjunction adj).counit.app X) := by
      intro X
      apply @isIso_of_reflects_iso _ _ _ _ _ _ _ (Comonad.forget adj.toComonad) ?_ _
      · change IsIso ((comparisonAdjunction adj).counit.app X).f
        rw [comparisonAdjunction_counit_f]
        change
          IsIso
            (IsLimit.conePointUniqueUpToIso (beckEqualizer X)
                (counitLimitOfPreservesEqualizer X)).inv
        exact (IsLimit.conePointUniqueUpToIso _ _).isIso_inv
    have : ∀ (Y : C), IsIso ((comparisonAdjunction adj).unit.app Y) := by
      intro Y
      rw [comparisonAdjunction_unit_app]
      change IsIso (IsLimit.conePointUniqueUpToIso _ ?_).inv
      infer_instance
      apply @unitEqualizerOfCoreflectsEqualizer _ _ _ _ _ _ _ _ ?_
      letI _ :
        F.IsCosplitPair (G.map (F.map (adj.unit.app Y)))
          (adj.unit.app (G.obj (F.obj Y))) :=
        ComonadicityInternal.main_pair_F_cosplit _ ((comparison adj).obj Y)
      infer_instance
    exact (comparisonAdjunction adj).toEquivalence.symm.isEquivalence_inverse

class CreatesLimitOfIsCosplitPair (F : C ⥤ D) where
  /-- If `f, g` is an `F`-cosplit pair, then `F` creates limits of `parallelPair f g`. -/
  out : ∀ {A B} (f g : A ⟶ B) [F.IsCosplitPair f g], CreatesLimit (parallelPair f g) F

instance {A B} (f g : A ⟶ B) [F.IsCosplitPair f g] [CreatesLimitOfIsCosplitPair F] :
    CreatesLimit (parallelPair f g) F := CreatesLimitOfIsCosplitPair.out f g

instance [CreatesLimitOfIsCosplitPair F] : ∀ (A : Coalgebra adj.toComonad),
    CreatesLimit (parallelPair (G.map A.a)
      (NatTrans.app adj.unit (G.obj A.A))) F :=
  fun _ => CreatesLimitOfIsCosplitPair.out _ _

def comonadicOfCreatesFSplitEqualizers [CreatesLimitOfIsCosplitPair F] :
    ComonadicLeftAdjoint F := by
  let I {A B} (f g : A ⟶ B) [F.IsCosplitPair f g] : HasLimit (parallelPair f g ⋙ F) := by
    apply @hasLimitOfIso _ _ _ _ _ _ ?_ (diagramIsoParallelPair.{v₁} _).symm
    exact inferInstanceAs <| HasEqualizer (F.map f) (F.map g)
  have : HasEqualizerOfIsCosplitPair F := ⟨fun _ _ => hasLimit_of_created (parallelPair _ _) F⟩
  have : PreservesLimitOfIsCosplitPair F := ⟨by intros; infer_instance⟩
  have : ReflectsLimitOfIsCosplitPair F := ⟨by intros; infer_instance⟩
  exact comonadicOfHasPreservesReflectsFSplitEqualizers adj

def comonadicOfHasPreservesFSplitEqualizersOfReflectsIsomorphisms [F.ReflectsIsomorphisms]
    [HasEqualizerOfIsCosplitPair F] [PreservesLimitOfIsCosplitPair F] :
    ComonadicLeftAdjoint F := by
  have : ReflectsLimitOfIsCosplitPair F := ⟨fun f g _ => by
    have := HasEqualizerOfIsCosplitPair.out F f g
    apply reflectsLimit_of_reflectsIsomorphisms⟩
  apply comonadicOfHasPreservesReflectsFSplitEqualizers adj

end BeckComonadicity

section CoreflexiveComonadicity

variable [HasCoreflexiveEqualizers C] [F.ReflectsIsomorphisms]

class PreservesLimitOfIsCoreflexivePair (F : C ⥤ D) where
  /-- `f, g` is a coreflexive pair, then `F` preserves limits of `parallelPair f g`. -/
  out : ∀ ⦃A B⦄ (f g : A ⟶ B) [IsCoreflexivePair f g], PreservesLimit (parallelPair f g) F

instance {A B} (f g : A ⟶ B) [IsCoreflexivePair f g] [PreservesLimitOfIsCoreflexivePair F] :
  PreservesLimit (parallelPair f g) F := PreservesLimitOfIsCoreflexivePair.out f g

instance [PreservesLimitOfIsCoreflexivePair F] : ∀ X : Coalgebra adj.toComonad,
    PreservesLimit (parallelPair (G.map X.a)
      (NatTrans.app adj.unit (G.obj X.A))) F :=
 fun _ => PreservesLimitOfIsCoreflexivePair.out _ _

variable [PreservesLimitOfIsCoreflexivePair F]

def comonadicOfHasPreservesCoreflexiveEqualizersOfReflectsIsomorphisms :
    ComonadicLeftAdjoint F where
  adj := adj
  eqv := by
    have : ∀ (X : adj.toComonad.Coalgebra), IsIso ((comparisonAdjunction adj).counit.app X) := by
      intro X
      apply
        @isIso_of_reflects_iso _ _ _ _ _ _ _ (Comonad.forget adj.toComonad) ?_ _
      · change IsIso ((comparisonAdjunction adj).counit.app X).f
        rw [comparisonAdjunction_counit_f]
        exact (IsLimit.conePointUniqueUpToIso (beckEqualizer X)
          (counitLimitOfPreservesEqualizer X)).isIso_inv
    have : ∀ (Y : C), IsIso ((comparisonAdjunction adj).unit.app Y) := by
      intro Y
      rw [comparisonAdjunction_unit_app]
      change IsIso (IsLimit.conePointUniqueUpToIso _ ?_).inv
      infer_instance
      have : IsCoreflexivePair (G.map (F.map (adj.unit.app Y)))
          (adj.unit.app (G.obj (F.obj Y))) := by
        apply IsCoreflexivePair.mk' (G.map (adj.counit.app _)) _ _
        · rw [← G.map_comp, ← G.map_id]
          exact congr_arg G.map (adj.left_triangle_components Y)
        · rw [← G.map_id]
          simp
      apply @unitEqualizerOfCoreflectsEqualizer _ _ _ _ _ _ _ _ ?_
      apply reflectsLimit_of_reflectsIsomorphisms
    exact (comparisonAdjunction adj).toEquivalence.symm.isEquivalence_inverse

end CoreflexiveComonadicity

end

end Comonad

end CategoryTheory
