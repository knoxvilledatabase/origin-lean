/-
Extracted from CategoryTheory/Bicategory/Functor/Prelax.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Prelax functors

This file defines lax prefunctors and prelax functors between bicategories. The point of these
definitions is to provide some common API that will be helpful in the development of both lax and
oplax functors.

## Main definitions

`PrelaxFunctorStruct B C`:

A PrelaxFunctorStruct `F` between quivers `B` and `C`, such that both have been equipped with quiver
structures on the hom-types, consists of
* a function between objects `F.obj : B → C`,
* a family of functions between 1-morphisms `F.map : (a ⟶ b) → (F.obj a ⟶ F.obj b)`,
* a family of functions between 2-morphisms `F.map₂ : (f ⟶ g) → (F.map f ⟶ F.map g)`,

`PrelaxFunctor B C`:

A prelax functor `F` between bicategories `B` and `C` is a `PrelaxFunctorStruct` such that the
associated prefunctors between the hom types are all functors. In other words, it is a
`PrelaxFunctorStruct` that satisfies
* `F.map₂ (𝟙 f) = 𝟙 (F.map f)`,
* `F.map₂ (η ≫ θ) = F.map₂ η ≫ F.map₂ θ`.

`mkOfHomFunctor`: constructs a `PrelaxFunctor` from a map on objects and functors between the
corresponding hom types.

-/

namespace CategoryTheory

open Category Bicategory

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

variable (B : Type u₁) [Quiver.{v₁} B] [∀ a b : B, Quiver.{w₁} (a ⟶ b)]

variable (C : Type u₂) [Quiver.{v₂} C] [∀ a b : C, Quiver.{w₂} (a ⟶ b)]

variable {D : Type u₃} [Quiver.{v₃} D] [∀ a b : D, Quiver.{w₃} (a ⟶ b)]

structure PrelaxFunctorStruct extends Prefunctor B C where
  /-- The action of a lax prefunctor on 2-morphisms. -/
  map₂ {a b : B} {f g : a ⟶ b} : (f ⟶ g) → (map f ⟶ map g)

initialize_simps_projections PrelaxFunctorStruct (+toPrefunctor, -obj, -map)

add_decl_doc PrelaxFunctorStruct.toPrefunctor

variable {B} {C}

namespace PrelaxFunctorStruct
