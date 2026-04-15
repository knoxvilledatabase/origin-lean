/-
Extracted from CategoryTheory/LocallyCartesianClosed/ExponentiableMorphism.lean
Genuine: 4 of 5 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Exponentiable morphisms

We define an exponentiable morphism `f : I ⟶ J` to be a morphism with a functorial choice of
pullbacks, given by `ChosenPullbacksAlong f`, together with a right adjoint to
the pullback functor `ChosenPullbacksAlong.pullback f : Over J ⥤ Over I`. We call this right adjoint
the pushforward functor along `f`.

## Main results

- The identity morphisms are exponentiable.
- The composition of exponentiable morphisms is exponentiable.

### TODO

- Any pullback of an exponentiable morphism is exponentiable.

-/

universe v u

namespace CategoryTheory

open Category MonoidalCategory Functor Adjunction

open ChosenPullbacksAlong

variable {C : Type u} [Category.{v} C]

class ExponentiableMorphism {I J : C} (f : I ⟶ J) [ChosenPullbacksAlong f] where
  /-- The pushforward functor -/
  pushforward : Over I ⥤ Over J
  /-- The pushforward functor is right adjoint to the pullback functor -/
  pullbackPushforwardAdj (f) : pullback f ⊣ pushforward

abbrev IsExponentiable [ChosenPullbacks C] : MorphismProperty C :=
  fun _ _ f ↦ IsLeftAdjoint (pullback f)

namespace ExponentiableMorphism

-- INSTANCE (free from Core): isExponentiable

variable {I J : C} (f : I ⟶ J) [ChosenPullbacksAlong f] [ExponentiableMorphism f]

def ev : pushforward f ⋙ pullback f ⟶ 𝟭 _ :=
  pullbackPushforwardAdj f |>.counit

def coev : 𝟭 _ ⟶ pullback f ⋙ pushforward f :=
  pullbackPushforwardAdj f |>.unit
