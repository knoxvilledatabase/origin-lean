/-
Extracted from CategoryTheory/Galois/IsFundamentalgroup.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Universal property of fundamental group

Let `C` be a Galois category with fiber functor `F`. While in informal mathematics, we tend to
identify known groups from other contexts (e.g. the absolute Galois group of a field) with
the automorphism group `Aut F` of certain fiber functors `F`, this causes friction in formalization.

Hence, in this file we develop conditions when a topological group `G` is canonically isomorphic to
the automorphism group `Aut F` of `F`. Consequently, the API for Galois categories and their fiber
functors should be stated in terms of an abstract topological group `G` satisfying
`IsFundamentalGroup` in the places where `Aut F` would appear.

## Main definition

Given a compact, topological group `G` with an action on `F.obj X` on each `X`, we say that
`G` is a fundamental group of `F` (`IsFundamentalGroup F G`), if

- `naturality`: the `G`-action on `F.obj X` is compatible with morphisms in `C`
- `transitive_of_isGalois`: `G` acts transitively on `F.obj X` for all Galois objects `X : C`
- `continuous_smul`: the action of `G` on `F.obj X` is continuous if `F.obj X` is equipped with the
  discrete topology for all `X : C`.
- `non_trivial'`: if `g : G` acts trivially on all `F.obj X`, then `g = 1`.

Given this data, we define `toAut F G : G →* Aut F` in the natural way.

## Main results

- `toAut_bijective`: `toAut F G` is a group isomorphism given `IsFundamentalGroup F G`.
- `toAut_isHomeomorph`: `toAut F G` is a homeomorphism given `IsFundamentalGroup F G`.

## TODO

- Develop further equivalent conditions, in particular, relate the condition `non_trivial` with
  `G` being a `T2Space`.

-/

universe u₁ u₂ w

namespace CategoryTheory

namespace PreGaloisCategory

open Limits Functor

variable {C : Type u₁} [Category.{u₂} C] (F : C ⥤ FintypeCat.{w})

variable (G : Type*) [Group G] [∀ X, MulAction G (F.obj X)]

class IsNaturalSMul : Prop where
  naturality (g : G) {X Y : C} (f : X ⟶ Y) (x : F.obj X) : F.map f (g • x) = g • F.map f x

set_option backward.privateInPublic true in

variable {G} in
