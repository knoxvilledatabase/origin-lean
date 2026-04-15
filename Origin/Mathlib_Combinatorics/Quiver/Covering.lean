/-
Extracted from Combinatorics/Quiver/Covering.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Covering

This file defines coverings of quivers as prefunctors that are bijective on the
so-called stars and costars at each vertex of the domain.

## Main definitions

* `Quiver.Star u` is the type of all arrows with source `u`;
* `Quiver.Costar u` is the type of all arrows with target `u`;
* `Prefunctor.star φ u` is the obvious function `star u → star (φ.obj u)`;
* `Prefunctor.costar φ u` is the obvious function `costar u → costar (φ.obj u)`;
* `Prefunctor.IsCovering φ` means that `φ.star u` and `φ.costar u` are bijections for all `u`;
* `Quiver.PathStar u` is the type of all paths with source `u`;
* `Prefunctor.pathStar u` is the obvious function `PathStar u → PathStar (φ.obj u)`.

## Main statements

* `Prefunctor.IsCovering.pathStar_bijective` states that if `φ` is a covering,
  then `φ.pathStar u` is a bijection for all `u`.
  In other words, every path in the codomain of `φ` lifts uniquely to its domain.

## TODO

Clean up the namespaces by renaming `Prefunctor` to `Quiver.Prefunctor`.

## Tags

Cover, covering, quiver, path, lift
-/

open Function Quiver

universe u v w

variable {U : Type _} [Quiver.{u} U] {V : Type _} [Quiver.{v} V] (φ : U ⥤q V) {W : Type _}
  [Quiver.{w} W] (ψ : V ⥤q W)

abbrev Quiver.Star (u : U) :=
  Σ v : U, u ⟶ v

protected abbrev Quiver.Star.mk {u v : U} (f : u ⟶ v) : Quiver.Star u :=
  ⟨_, f⟩

abbrev Quiver.Costar (v : U) :=
  Σ u : U, u ⟶ v

protected abbrev Quiver.Costar.mk {u v : U} (f : u ⟶ v) : Quiver.Costar v :=
  ⟨_, f⟩
