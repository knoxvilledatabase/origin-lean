/-
Extracted from CategoryTheory/Monad/Monadicity.lean
Genuine: 21 of 33 | Dissolved: 0 | Infrastructure: 12
-/
import Origin.Core
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.Reflexive
import Mathlib.CategoryTheory.Monad.Coequalizer
import Mathlib.CategoryTheory.Monad.Limits

/-!
# Monadicity theorems

We prove monadicity theorems which can establish a given functor is monadic. In particular, we
show three versions of Beck's monadicity theorem, and the reflexive (crude) monadicity theorem:

`G` is a monadic right adjoint if it has a left adjoint, and:

* `D` has, `G` preserves and reflects `G`-split coequalizers, see
  `CategoryTheory.Monad.monadicOfHasPreservesReflectsGSplitCoequalizers`
* `G` creates `G`-split coequalizers, see
  `CategoryTheory.Monad.monadicOfCreatesGSplitCoequalizers`
  (The converse of this is also shown, see
   `CategoryTheory.Monad.createsGSplitCoequalizersOfMonadic`)
* `D` has and `G` preserves `G`-split coequalizers, and `G` reflects isomorphisms, see
  `CategoryTheory.Monad.monadicOfHasPreservesGSplitCoequalizersOfReflectsIsomorphisms`
* `D` has and `G` preserves reflexive coequalizers, and `G` reflects isomorphisms, see
  `CategoryTheory.Monad.monadicOfHasPreservesReflexiveCoequalizersOfReflectsIsomorphisms`

This file has been adapted to `Mathlib.CategoryTheory.Monad.Comonadicity`.
Please try to keep them in sync.

## Tags

Beck, monadicity, descent

-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Monad

open Limits

noncomputable section

namespace MonadicityInternal

variable {C : Type u₁} {D : Type u₂}

variable [Category.{v₁} C] [Category.{v₁} D]

variable {G : D ⥤ C} {F : C ⥤ D} (adj : F ⊣ G)

instance main_pair_reflexive (A : adj.toMonad.Algebra) :
    IsReflexivePair (F.map A.a) (adj.counit.app (F.obj A.A)) := by
  apply IsReflexivePair.mk' (F.map (adj.unit.app _)) _ _
  · rw [← F.map_comp, ← F.map_id]
    exact congr_arg F.map A.unit
  · rw [adj.left_triangle_components]
    rfl

instance main_pair_G_split (A : adj.toMonad.Algebra) :
    G.IsSplitPair (F.map A.a)
      (adj.counit.app (F.obj A.A)) where
  splittable := ⟨_, _, ⟨beckSplitCoequalizer A⟩⟩

def comparisonLeftAdjointObj (A : adj.toMonad.Algebra)
    [HasCoequalizer (F.map A.a) (adj.counit.app _)] : D :=
  coequalizer (F.map A.a) (adj.counit.app _)

set_option linter.unusedVariables false in

@[simps!]
def comparisonLeftAdjointHomEquiv (A : adj.toMonad.Algebra) (B : D)
    [HasCoequalizer (F.map A.a) (adj.counit.app (F.obj A.A))] :
    (comparisonLeftAdjointObj adj A ⟶ B) ≃ (A ⟶ (comparison adj).obj B) :=
  calc
    (comparisonLeftAdjointObj adj A ⟶ B) ≃ { f : F.obj A.A ⟶ B // _ } :=
      Cofork.IsColimit.homIso (colimit.isColimit _) B
    _ ≃ { g : A.A ⟶ G.obj B // G.map (F.map g) ≫ G.map (adj.counit.app B) = A.a ≫ g } := by
      refine (adj.homEquiv _ _).subtypeEquiv ?_
      intro f
      rw [← (adj.homEquiv _ _).injective.eq_iff, Adjunction.homEquiv_naturality_left,
        adj.homEquiv_unit, adj.homEquiv_unit, G.map_comp]
      dsimp
      rw [adj.right_triangle_components_assoc, ← G.map_comp, F.map_comp, Category.assoc,
        adj.counit_naturality, adj.left_triangle_components_assoc]
      apply eq_comm
    _ ≃ (A ⟶ (comparison adj).obj B) :=
      { toFun := fun g =>
          { f := _
            h := g.prop }
        invFun := fun f => ⟨f.f, f.h⟩
        left_inv := fun g => by ext; rfl
        right_inv := fun f => by ext; rfl }

def leftAdjointComparison
    [∀ A : adj.toMonad.Algebra, HasCoequalizer (F.map A.a)
      (adj.counit.app (F.obj A.A))] :
    adj.toMonad.Algebra ⥤ D := by
  refine
    Adjunction.leftAdjointOfEquiv (G := comparison adj)
      (F_obj := fun A => comparisonLeftAdjointObj adj A) (fun A B => ?_) ?_
  · apply comparisonLeftAdjointHomEquiv
  · intro A B B' g h
    ext1
    -- Porting note: the goal was previously closed by the following, which succeeds until
    -- `Category.assoc`.
    -- dsimp [comparisonLeftAdjointHomEquiv]
    -- rw [← adj.homEquiv_naturality_right, Category.assoc]
    simp [Cofork.IsColimit.homIso, Adjunction.homEquiv_unit]

@[simps! counit]
def comparisonAdjunction
    [∀ A : adj.toMonad.Algebra, HasCoequalizer (F.map A.a)
      (adj.counit.app (F.obj A.A))] :
    leftAdjointComparison adj ⊣ comparison adj :=
  Adjunction.adjunctionOfEquivLeft _ _

variable {adj}

theorem comparisonAdjunction_unit_f_aux
    [∀ A : adj.toMonad.Algebra, HasCoequalizer (F.map A.a)
      (adj.counit.app (F.obj A.A))]
    (A : adj.toMonad.Algebra) :
    ((comparisonAdjunction adj).unit.app A).f =
      adj.homEquiv A.A _
        (coequalizer.π (F.map A.a) (adj.counit.app (F.obj A.A))) :=
  congr_arg (adj.homEquiv _ _) (Category.comp_id _)

@[simps! pt]
def unitCofork (A : adj.toMonad.Algebra)
    [HasCoequalizer (F.map A.a) (adj.counit.app (F.obj A.A))] :
    Cofork (G.map (F.map A.a)) (G.map (adj.counit.app (F.obj A.A))) :=
  Cofork.ofπ (G.map (coequalizer.π (F.map A.a) (adj.counit.app (F.obj A.A))))
    (by
      change _ = G.map _ ≫ _
      rw [← G.map_comp, coequalizer.condition, G.map_comp])

@[simp]
theorem unitCofork_π (A : adj.toMonad.Algebra)
    [HasCoequalizer (F.map A.a) (adj.counit.app (F.obj A.A))] :
    (unitCofork A).π = G.map (coequalizer.π (F.map A.a) (adj.counit.app (F.obj A.A))) :=
  rfl

theorem comparisonAdjunction_unit_f
    [∀ A : adj.toMonad.Algebra, HasCoequalizer (F.map A.a)
      (adj.counit.app (F.obj A.A))]
    (A : adj.toMonad.Algebra) :
    ((comparisonAdjunction adj).unit.app A).f = (beckCoequalizer A).desc (unitCofork A) := by
  apply Limits.Cofork.IsColimit.hom_ext (beckCoequalizer A)
  rw [Cofork.IsColimit.π_desc]
  dsimp only [beckCofork_π, unitCofork_π]
  rw [comparisonAdjunction_unit_f_aux, ← adj.homEquiv_naturality_left A.a, coequalizer.condition,
    adj.homEquiv_naturality_right, adj.homEquiv_unit, Category.assoc]
  apply adj.right_triangle_components_assoc

variable (adj)

@[simps!]
def counitCofork (B : D) :
    Cofork (F.map (G.map (adj.counit.app B)))
      (adj.counit.app (F.obj (G.obj B))) :=
  Cofork.ofπ (adj.counit.app B) (adj.counit_naturality _)

variable {adj} in

def unitColimitOfPreservesCoequalizer (A : adj.toMonad.Algebra)
    [HasCoequalizer (F.map A.a) (adj.counit.app (F.obj A.A))]
    [PreservesColimit (parallelPair (F.map A.a) (adj.counit.app (F.obj A.A))) G] :
    IsColimit (unitCofork (G := G) A) :=
  isColimitOfHasCoequalizerOfPreservesColimit G _ _

def counitCoequalizerOfReflectsCoequalizer (B : D)
    [ReflectsColimit (parallelPair (F.map (G.map (adj.counit.app B)))
      (adj.counit.app (F.obj (G.obj B)))) G] :
    IsColimit (counitCofork (adj := adj) B) :=
  isColimitOfIsColimitCoforkMap G _ (beckCoequalizer ((comparison adj).obj B))

instance

    [∀ A : adj.toMonad.Algebra, HasCoequalizer (F.map A.a) (adj.counit.app (F.obj A.A))]

    (B : D) : HasColimit (parallelPair

      (F.map (G.map (NatTrans.app adj.counit B)))

      (NatTrans.app adj.counit (F.obj (G.obj B)))) :=

  inferInstanceAs <| HasCoequalizer

    (F.map ((comparison adj).obj B).a)

    (adj.counit.app (F.obj ((comparison adj).obj B).A))

theorem comparisonAdjunction_counit_app
    [∀ A : adj.toMonad.Algebra, HasCoequalizer (F.map A.a) (adj.counit.app (F.obj A.A))] (B : D) :
    (comparisonAdjunction adj).counit.app B = colimit.desc _ (counitCofork adj B) := by
  apply coequalizer.hom_ext
  change
    coequalizer.π _ _ ≫ coequalizer.desc ((adj.homEquiv _ B).symm (𝟙 _)) _ =
      coequalizer.π _ _ ≫ coequalizer.desc _ _
  simp [Adjunction.homEquiv_counit]

end MonadicityInternal

open CategoryTheory Adjunction Monad MonadicityInternal

variable {C : Type u₁} {D : Type u₂}

variable [Category.{v₁} C] [Category.{v₁} D]

variable {G : D ⥤ C} {F : C ⥤ D} (adj : F ⊣ G)

variable (G) in

def createsGSplitCoequalizersOfMonadic [MonadicRightAdjoint G] ⦃A B⦄ (f g : A ⟶ B)
    [G.IsSplitPair f g] : CreatesColimit (parallelPair f g) G := by
  apply (config := {allowSynthFailures := true}) monadicCreatesColimitOfPreservesColimit
    -- Porting note: oddly (config := {allowSynthFailures := true}) had no effect here and below
  all_goals
    apply @preservesColimit_of_iso_diagram _ _ _ _ _ _ _ _ _ (diagramIsoParallelPair.{v₁} _).symm ?_
    dsimp
    infer_instance

section BeckMonadicity

class HasCoequalizerOfIsSplitPair (G : D ⥤ C) : Prop where
  out : ∀ {A B} (f g : A ⟶ B) [G.IsSplitPair f g], HasCoequalizer f g

instance [HasCoequalizerOfIsSplitPair G] : ∀ (A : Algebra adj.toMonad),
    HasCoequalizer (F.map A.a)
      (adj.counit.app (F.obj A.A)) :=
  fun _ => HasCoequalizerOfIsSplitPair.out G _ _

class PreservesColimitOfIsSplitPair (G : D ⥤ C) where
  out : ∀ {A B} (f g : A ⟶ B) [G.IsSplitPair f g], PreservesColimit (parallelPair f g) G

instance {A B} (f g : A ⟶ B) [G.IsSplitPair f g] [PreservesColimitOfIsSplitPair G] :
    PreservesColimit (parallelPair f g) G := PreservesColimitOfIsSplitPair.out f g

instance [PreservesColimitOfIsSplitPair G] : ∀ (A : Algebra adj.toMonad),
   PreservesColimit (parallelPair (F.map A.a)
      (NatTrans.app adj.counit (F.obj A.A))) G :=
  fun _ => PreservesColimitOfIsSplitPair.out _ _

class ReflectsColimitOfIsSplitPair (G : D ⥤ C) where
  out : ∀ {A B} (f g : A ⟶ B) [G.IsSplitPair f g], ReflectsColimit (parallelPair f g) G

instance {A B} (f g : A ⟶ B) [G.IsSplitPair f g] [ReflectsColimitOfIsSplitPair G] :
    ReflectsColimit (parallelPair f g) G := ReflectsColimitOfIsSplitPair.out f g

instance [ReflectsColimitOfIsSplitPair G] : ∀ (A : Algebra adj.toMonad),
    ReflectsColimit (parallelPair (F.map A.a)
      (NatTrans.app adj.counit (F.obj A.A))) G :=
  fun _ => ReflectsColimitOfIsSplitPair.out _ _

def monadicOfHasPreservesReflectsGSplitCoequalizers [HasCoequalizerOfIsSplitPair G]
    [PreservesColimitOfIsSplitPair G] [ReflectsColimitOfIsSplitPair G] :
    MonadicRightAdjoint G where
  adj := adj
  eqv := by
    have : ∀ (X : Algebra adj.toMonad), IsIso ((comparisonAdjunction adj).unit.app X) := by
      intro X
      apply @isIso_of_reflects_iso _ _ _ _ _ _ _ (Monad.forget adj.toMonad) ?_ _
      · change IsIso ((comparisonAdjunction adj).unit.app X).f
        rw [comparisonAdjunction_unit_f]
        change
          IsIso
            (IsColimit.coconePointUniqueUpToIso (beckCoequalizer X)
                (unitColimitOfPreservesCoequalizer X)).hom
        exact (IsColimit.coconePointUniqueUpToIso _ _).isIso_hom
    have : ∀ (Y : D), IsIso ((comparisonAdjunction adj).counit.app Y) := by
      intro Y
      rw [comparisonAdjunction_counit_app]
      -- Porting note: passing instances through
      change IsIso (IsColimit.coconePointUniqueUpToIso _ ?_).hom
      infer_instance
      -- Porting note: passing instances through
      apply @counitCoequalizerOfReflectsCoequalizer _ _ _ _ _ _ _ _ ?_
      letI _ :
        G.IsSplitPair (F.map (G.map (adj.counit.app Y)))
          (adj.counit.app (F.obj (G.obj Y))) :=
        MonadicityInternal.main_pair_G_split _ ((comparison adj).obj Y)
      infer_instance
    exact (comparisonAdjunction adj).toEquivalence.isEquivalence_inverse

class CreatesColimitOfIsSplitPair (G : D ⥤ C) where
  out : ∀ {A B} (f g : A ⟶ B) [G.IsSplitPair f g], CreatesColimit (parallelPair f g) G

instance {A B} (f g : A ⟶ B) [G.IsSplitPair f g] [CreatesColimitOfIsSplitPair G] :
    CreatesColimit (parallelPair f g) G := CreatesColimitOfIsSplitPair.out f g

instance [CreatesColimitOfIsSplitPair G] : ∀ (A : Algebra adj.toMonad),
    CreatesColimit (parallelPair (F.map A.a)
      (NatTrans.app adj.counit (F.obj A.A))) G :=
  fun _ => CreatesColimitOfIsSplitPair.out _ _

def monadicOfCreatesGSplitCoequalizers [CreatesColimitOfIsSplitPair G] :
    MonadicRightAdjoint G := by
  let I {A B} (f g : A ⟶ B) [G.IsSplitPair f g] : HasColimit (parallelPair f g ⋙ G) := by
    apply @hasColimitOfIso _ _ _ _ _ _ ?_ (diagramIsoParallelPair.{v₁} _)
    exact inferInstanceAs <| HasCoequalizer (G.map f) (G.map g)
  have : HasCoequalizerOfIsSplitPair G := ⟨fun _ _ => hasColimit_of_created (parallelPair _ _) G⟩
  have : PreservesColimitOfIsSplitPair G := ⟨by intros; infer_instance⟩
  have : ReflectsColimitOfIsSplitPair G := ⟨by intros; infer_instance⟩
  exact monadicOfHasPreservesReflectsGSplitCoequalizers adj

def monadicOfHasPreservesGSplitCoequalizersOfReflectsIsomorphisms [G.ReflectsIsomorphisms]
    [HasCoequalizerOfIsSplitPair G] [PreservesColimitOfIsSplitPair G] :
    MonadicRightAdjoint G := by
  have : ReflectsColimitOfIsSplitPair G := ⟨fun f g _ => by
    have := HasCoequalizerOfIsSplitPair.out G f g
    apply reflectsColimit_of_reflectsIsomorphisms⟩
  apply monadicOfHasPreservesReflectsGSplitCoequalizers adj

end BeckMonadicity

section ReflexiveMonadicity

variable [HasReflexiveCoequalizers D] [G.ReflectsIsomorphisms]

class PreservesColimitOfIsReflexivePair (G : C ⥤ D) where
  out : ∀ ⦃A B⦄ (f g : A ⟶ B) [IsReflexivePair f g], PreservesColimit (parallelPair f g) G

instance {A B} (f g : A ⟶ B) [IsReflexivePair f g] [PreservesColimitOfIsReflexivePair G] :
  PreservesColimit (parallelPair f g) G := PreservesColimitOfIsReflexivePair.out f g

instance [PreservesColimitOfIsReflexivePair G] : ∀ X : Algebra adj.toMonad,
    PreservesColimit (parallelPair (F.map X.a)
      (NatTrans.app adj.counit (F.obj X.A))) G :=
 fun _ => PreservesColimitOfIsReflexivePair.out _ _

variable [PreservesColimitOfIsReflexivePair G]

def monadicOfHasPreservesReflexiveCoequalizersOfReflectsIsomorphisms : MonadicRightAdjoint G where
  adj := adj
  eqv := by
    have : ∀ (X : Algebra adj.toMonad), IsIso ((comparisonAdjunction adj).unit.app X) := by
      intro X
      apply
        @isIso_of_reflects_iso _ _ _ _ _ _ _ (Monad.forget adj.toMonad) ?_ _
      · change IsIso ((comparisonAdjunction adj).unit.app X).f
        rw [comparisonAdjunction_unit_f]
        exact (IsColimit.coconePointUniqueUpToIso (beckCoequalizer X)
          (unitColimitOfPreservesCoequalizer X)).isIso_hom
    have : ∀ (Y : D), IsIso ((comparisonAdjunction adj).counit.app Y) := by
      intro Y
      rw [comparisonAdjunction_counit_app]
      -- Porting note: passing instances through
      change IsIso (IsColimit.coconePointUniqueUpToIso _ ?_).hom
      infer_instance
      -- Porting note: passing instances through
      apply @counitCoequalizerOfReflectsCoequalizer _ _ _ _ _ _ _ _ ?_
      apply reflectsColimit_of_reflectsIsomorphisms
    exact (comparisonAdjunction adj).toEquivalence.isEquivalence_inverse

end ReflexiveMonadicity

end

end Monad

end CategoryTheory
