/-
Extracted from CategoryTheory/Limits/Preserves/Shapes/Equalizers.lean
Genuine: 6 of 6 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Preserving (co)equalizers

Constructions to relate the notions of preserving (co)equalizers and reflecting (co)equalizers
to concrete (co)forks.

In particular, we show that `equalizerComparison f g G` is an isomorphism iff `G` preserves
the limit of the parallel pair `f,g`, as well as the dual result.
-/

noncomputable section

universe w v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C]

variable {D : Type u₂} [Category.{v₂} D]

variable (G : C ⥤ D)

namespace CategoryTheory.Limits

section Equalizers

variable {X Y Z : C} {f g : X ⟶ Y} {h : Z ⟶ X} (w : h ≫ f = h ≫ g)

def isLimitMapConeForkEquiv :
    IsLimit (G.mapCone (Fork.ofι h w)) ≃
      IsLimit (Fork.ofι (G.map h) (by simp only [← G.map_comp, w]) : Fork (G.map f) (G.map g)) :=
  (IsLimit.postcomposeHomEquiv (diagramIsoParallelPair _) _).symm.trans
    (IsLimit.equivIsoLimit (Fork.ext (Iso.refl _) (by simp [Fork.ι])))

def isLimitForkMapOfIsLimit [PreservesLimit (parallelPair f g) G] (l : IsLimit (Fork.ofι h w)) :
    IsLimit (Fork.ofι (G.map h) (by simp only [← G.map_comp, w]) : Fork (G.map f) (G.map g)) :=
  isLimitMapConeForkEquiv G w (isLimitOfPreserves G l)

def isLimitOfIsLimitForkMap [ReflectsLimit (parallelPair f g) G]
    (l : IsLimit (Fork.ofι (G.map h) (by simp only [← G.map_comp, w]) : Fork (G.map f) (G.map g))) :
    IsLimit (Fork.ofι h w) :=
  isLimitOfReflects G ((isLimitMapConeForkEquiv G w).symm l)

variable (f g)

variable [HasEqualizer f g]

def isLimitOfHasEqualizerOfPreservesLimit [PreservesLimit (parallelPair f g) G] :
    IsLimit (Fork.ofι
      (G.map (equalizer.ι f g)) (by simp only [← G.map_comp]; rw [equalizer.condition]) :
      Fork (G.map f) (G.map g)) :=
  isLimitForkMapOfIsLimit G _ (equalizerIsEqualizer f g)

variable [HasEqualizer (G.map f) (G.map g)]

lemma PreservesEqualizer.of_iso_comparison [i : IsIso (equalizerComparison f g G)] :
    PreservesLimit (parallelPair f g) G := by
  apply preservesLimit_of_preserves_limit_cone (equalizerIsEqualizer f g)
  apply (isLimitMapConeForkEquiv _ _).symm _
  exact @IsLimit.ofPointIso _ _ _ _ _ _ _ (limit.isLimit (parallelPair (G.map f) (G.map g))) i

variable [PreservesLimit (parallelPair f g) G]

def PreservesEqualizer.iso : G.obj (equalizer f g) ≅ equalizer (G.map f) (G.map g) :=
  IsLimit.conePointUniqueUpToIso (isLimitOfHasEqualizerOfPreservesLimit G f g) (limit.isLimit _)
