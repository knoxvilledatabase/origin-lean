/-
Extracted from CategoryTheory/Join/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Joins of categories

Given categories `C, D`, this file constructs a category `C ⋆ D`. Its objects are either
objects of `C` or objects of `D`, morphisms between objects of `C` are morphisms in `C`,
morphisms between objects of `D` are morphisms in `D`, and finally, given `c : C` and `d : D`,
there is a unique morphism `c ⟶ d` in `C ⋆ D`.

## Main constructions

* `Join.edge c d`: the unique map from `c` to `d`.
* `Join.inclLeft : C ⥤ C ⋆ D`, the left inclusion. Its action on morphisms is the main entry point
  to construct maps in `C ⋆ D` between objects coming from `C`.
* `Join.inclRight : D ⥤ C ⋆ D`, the right inclusion. Its action on morphisms is the main entry point
  to construct maps in `C ⋆ D` between objects coming from `D`.
* `Join.mkFunctor`, A constructor for functors out of a join of categories.
* `Join.mkNatTrans`, A constructor for natural transformations between functors out of a join
  of categories.
* `Join.mkNatIso`, A constructor for natural isomorphisms between functors out of a join
  of categories.

## References

* [Kerodon: section 1.4.3.2](https://kerodon.net/tag/0160)

-/

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

namespace CategoryTheory

open Functor

inductive Join (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D] : Type (max u₁ u₂)
  | left : C → Join C D
  | right : D → Join C D

attribute [aesop safe cases (rule_sets := [CategoryTheory])] Join

namespace Join
