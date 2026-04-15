/-
Extracted from CategoryTheory/Limits/Preserves/Shapes/Pullbacks.lean
Genuine: 9 of 9 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Preserving pullbacks

Constructions to relate the notions of preserving pullbacks and reflecting pullbacks to concrete
pullback cones.

In particular, we show that `pullbackComparison G f g` is an isomorphism iff `G` preserves
the pullback of `f` and `g`.

The dual is also given.

## TODO

* Generalise to wide pullbacks

-/

noncomputable section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Functor

namespace CategoryTheory.Limits

section Pullback

variable {C : Type u₁} [Category.{v₁} C]

variable {D : Type u₂} [Category.{v₂} D]

namespace PullbackCone

variable {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g) (G : C ⥤ D)

abbrev map : PullbackCone (G.map f) (G.map g) :=
  PullbackCone.mk (G.map c.fst) (G.map c.snd)
    (by simpa using G.congr_map c.condition)

def isLimitMapConeEquiv :
    IsLimit (mapCone G c) ≃ IsLimit (c.map G) :=
  (IsLimit.postcomposeHomEquiv (diagramIsoCospan.{v₂} _) _).symm.trans <|
    IsLimit.equivIsoLimit <| by
      refine PullbackCone.ext (Iso.refl _) ?_ ?_
      · dsimp only [fst]
        simp
      · dsimp only [snd]
        simp

end PullbackCone

variable (G : C ⥤ D)

variable {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {h : W ⟶ X} {k : W ⟶ Y} (comm : h ≫ f = k ≫ g)

def isLimitMapConePullbackConeEquiv :
    IsLimit (mapCone G (PullbackCone.mk h k comm)) ≃
      IsLimit
        (PullbackCone.mk (G.map h) (G.map k) (by simp only [← G.map_comp, comm]) :
          PullbackCone (G.map f) (G.map g)) :=
  (PullbackCone.mk _ _ comm).isLimitMapConeEquiv G

def isLimitPullbackConeMapOfIsLimit [PreservesLimit (cospan f g) G]
    (l : IsLimit (PullbackCone.mk h k comm)) :
    have : G.map h ≫ G.map f = G.map k ≫ G.map g := by rw [← G.map_comp, ← G.map_comp, comm]
    IsLimit (PullbackCone.mk (G.map h) (G.map k) this) :=
  (PullbackCone.isLimitMapConeEquiv _ G).1 (isLimitOfPreserves G l)

def isLimitOfIsLimitPullbackConeMap [ReflectsLimit (cospan f g) G]
    (l : IsLimit (PullbackCone.mk (G.map h) (G.map k) (show G.map h ≫ G.map f = G.map k ≫ G.map g
    from by simp only [← G.map_comp, comm]))) : IsLimit (PullbackCone.mk h k comm) :=
  isLimitOfReflects G
    ((PullbackCone.isLimitMapConeEquiv (PullbackCone.mk _ _ comm) G).2 l)

variable (f g) [PreservesLimit (cospan f g) G]

def isLimitOfHasPullbackOfPreservesLimit [HasPullback f g] :
    have : G.map (pullback.fst f g) ≫ G.map f = G.map (pullback.snd f g) ≫ G.map g := by
      simp only [← G.map_comp, pullback.condition]
    IsLimit (PullbackCone.mk (G.map (pullback.fst f g)) (G.map (pullback.snd f g)) this) :=
  isLimitPullbackConeMapOfIsLimit G _ (pullbackIsPullback f g)

lemma preservesPullback_symmetry : PreservesLimit (cospan g f) G where
  preserves {c} hc := ⟨by
    apply (IsLimit.postcomposeHomEquiv (diagramIsoCospan.{v₂} _) _).toFun
    apply IsLimit.ofIsoLimit _ (PullbackCone.isoMk _).symm
    apply PullbackCone.isLimitOfFlip
    apply (isLimitMapConePullbackConeEquiv _ _).toFun
    · refine @isLimitOfPreserves _ _ _ _ _ _ _ _ _ ?_ ?_
      · apply PullbackCone.isLimitOfFlip
        apply IsLimit.ofIsoLimit _ (PullbackCone.isoMk _)
        exact (IsLimit.postcomposeHomEquiv (diagramIsoCospan.{v₁} _) _).invFun hc
      · dsimp
        infer_instance
    · exact
        (c.π.naturality WalkingCospan.Hom.inr).symm.trans
          (c.π.naturality WalkingCospan.Hom.inl :)⟩

theorem hasPullback_of_preservesPullback [HasPullback f g] : HasPullback (G.map f) (G.map g) :=
  ⟨⟨⟨_, isLimitPullbackConeMapOfIsLimit G _ (pullbackIsPullback _ _)⟩⟩⟩

variable [HasPullback f g] [HasPullback (G.map f) (G.map g)]

def PreservesPullback.iso : G.obj (pullback f g) ≅ pullback (G.map f) (G.map g) :=
  IsLimit.conePointUniqueUpToIso (isLimitOfHasPullbackOfPreservesLimit G f g) (limit.isLimit _)
