/-
Extracted from CategoryTheory/ConcreteCategory/Forget.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Forgetful functors

A concrete category is a category `C` where the objects and morphisms correspond with types and
(bundled) functions between these types, see the file
`Mathlib.CategoryTheory.ConcreteCategory.Basic`

Each concrete category `C` comes with a canonical faithful functor `forget C : C ⥤ Type*`.
We impose no restrictions on the category `C`, so `Type` has the identity forgetful functor.

We say that a concrete category `C` admits a *forgetful functor* to a concrete category `D`, if it
has a functor `forget₂ C D : C ⥤ D` such that `(forget₂ C D) ⋙ (forget D) = forget C`, see
`class HasForget₂`.  Due to `Faithful.div_comp`, it suffices to verify that `forget₂.obj` and
`forget₂.map` agree with the equality above; then `forget₂` will satisfy the functor laws
automatically, see `HasForget₂.mk'`.

We say that a concrete category `C` admits a *forgetful functor* to a concrete category `D`, if it
has a functor `forget₂ C D : C ⥤ D` such that `(forget₂ C D) ⋙ (forget D) = forget C`, see
`class HasForget₂`.  Due to `Faithful.div_comp`, it suffices to verify that `forget₂.obj` and
`forget₂.map` agree with the equality above; then `forget₂` will satisfy the functor laws
automatically, see `HasForget₂.mk'`.

## References

See [Ahrens and Lumsdaine, *Displayed Categories*][ahrens2017] for
related work.
-/

namespace CategoryTheory

universe w u

variable (C : Type*) [Category* C] {FC : outParam <| C → C → Type*} {CC : outParam <| C → Type w}
    [outParam <| ∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{w} C FC]

abbrev forget : C ⥤ Type w where
  obj X := ToType X
  map f := TypeCat.ofHom f

-- INSTANCE (free from Core): :

variable {C}
