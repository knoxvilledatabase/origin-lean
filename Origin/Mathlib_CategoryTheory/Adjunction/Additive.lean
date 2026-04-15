/-
Extracted from CategoryTheory/Adjunction/Additive.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Adjunctions between additive functors.

This provides some results and constructions for adjunctions between functors on
preadditive categories:
* If one of the adjoint functors is additive, so is the other.
* If one of the adjoint functors is additive, the equivalence `Adjunction.homEquiv` lifts to
  an additive equivalence `Adjunction.homAddEquiv`.
* We also give a version of this additive equivalence as an isomorphism of `preadditiveYoneda`
  functors (analogous to `Adjunction.compYonedaIso`), in `Adjunction.compPreadditiveYonedaIso`.

-/

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

namespace Adjunction

open CategoryTheory Category Functor

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] [Preadditive C]
  [Preadditive D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

include adj

set_option backward.isDefEq.respectTransparency false in

lemma right_adjoint_additive [F.Additive] : G.Additive where
  map_add {X Y} f g := (adj.homEquiv _ _).symm.injective (by simp [homEquiv_counit])

set_option backward.isDefEq.respectTransparency false in

lemma left_adjoint_additive [G.Additive] : F.Additive where
  map_add {X Y} f g := (adj.homEquiv _ _).injective (by simp [homEquiv_unit])

variable [F.Additive]

def homAddEquiv (X : C) (Y : D) : AddEquiv (F.obj X ⟶ Y) (X ⟶ G.obj Y) :=
  { adj.homEquiv _ _ with
    map_add' _ _ := by
      have := adj.right_adjoint_additive
      simp [homEquiv_apply] }
