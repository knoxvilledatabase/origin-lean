/-
Extracted from CategoryTheory/Limits/Shapes/WideEqualizers.lean
Genuine: 3 of 6 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Wide equalizers and wide coequalizers

This file defines wide (co)equalizers as special cases of (co)limits.

A wide equalizer for the family of morphisms `X ⟶ Y` indexed by `J` is the categorical
generalization of the subobject `{a ∈ A | ∀ j₁ j₂, f(j₁, a) = f(j₂, a)}`. Note that if `J` has
fewer than two morphisms this condition is trivial, so some lemmas and definitions assume `J` is
nonempty.

## Main definitions

* `WalkingParallelFamily` is the indexing category used for wide (co)equalizer diagrams
* `parallelFamily` is a functor from `WalkingParallelFamily` to our category `C`.
* a `Trident` is a cone over a parallel family.
  * there is really only one interesting morphism in a trident: the arrow from the vertex of the
    trident to the domain of f and g. It is called `Trident.ι`.
* a `wideEqualizer` is now just a `limit (parallelFamily f)`

Each of these has a dual.

## Main statements

* `wideEqualizer.ι_mono` states that every wideEqualizer map is a monomorphism

## Implementation notes
As with the other special shapes in the limits library, all the definitions here are given as
`abbrev`s of the general statements for limits, so all the `simp` lemmas and theorems about
general limits can be used.

## References

* [F. Borceux, *Handbook of Categorical Algebra 1*][borceux-vol1]
-/

noncomputable section

namespace CategoryTheory.Limits

open CategoryTheory

universe w v u u₂

variable {J : Type w}

inductive WalkingParallelFamily (J : Type w) : Type w
  | zero : WalkingParallelFamily J
  | one : WalkingParallelFamily J

deriving Inhabited

open WalkingParallelFamily

-- INSTANCE (free from Core): :

set_option genSizeOfSpec false in

inductive WalkingParallelFamily.Hom (J : Type w) :
  WalkingParallelFamily J → WalkingParallelFamily J → Type w
  | id : ∀ X : WalkingParallelFamily.{w} J, WalkingParallelFamily.Hom J X X
  | line : J → WalkingParallelFamily.Hom J zero one
  deriving DecidableEq

-- INSTANCE (free from Core): (J

open WalkingParallelFamily.Hom

def WalkingParallelFamily.Hom.comp :
    ∀ {X Y Z : WalkingParallelFamily J} (_ : WalkingParallelFamily.Hom J X Y)
      (_ : WalkingParallelFamily.Hom J Y Z), WalkingParallelFamily.Hom J X Z
  | _, _, _, id _, h => h
  | _, _, _, line j, id one => line j

attribute [local aesop safe cases] WalkingParallelFamily.Hom

-- INSTANCE (free from Core): WalkingParallelFamily.category
