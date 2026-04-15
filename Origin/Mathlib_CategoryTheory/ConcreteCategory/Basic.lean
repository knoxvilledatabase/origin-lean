/-
Extracted from CategoryTheory/ConcreteCategory/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Concrete categories

A concrete category is a category `C` where the objects and morphisms correspond with types and
(bundled) functions between these types. We define concrete categories using
`class ConcreteCategory`. To convert an object to a type, write `ToType`. To convert a morphism
to a (bundled) function, write `hom`.

Each concrete category `C` comes with a canonical faithful functor `forget C : C ⥤ Type*`,
see the file `Mathlib.CategoryTheory.ConcreteCategory.Forget`

## Implementation notes

We do not use `CoeSort` to convert objects in a concrete category to types, since this would lead
to elaboration mismatches between results taking a `[ConcreteCategory C]` instance and specific
types `C` that hold a `ConcreteCategory C` instance: the first gets a literal `CoeSort.coe` and
the second gets unfolded to the actual `coe` field.

`ToType` and `ToHom` are `abbrev`s so that we do not need to copy over instances such as `Ring`
or `RingHomClass` respectively.

## References

See [Ahrens and Lumsdaine, *Displayed Categories*][ahrens2017] for
related work.
-/

assert_not_exists CategoryTheory.CommSq CategoryTheory.Adjunction

universe w w' v v' v'' u u' u''

namespace CategoryTheory

section ConcreteCategory

class ConcreteCategory (C : Type u) [Category.{v} C]
    (FC : outParam <| C → C → Type*) {CC : outParam <| C → Type w}
    [outParam <| ∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] where
  /-- Convert a morphism of `C` to a bundled function. -/
  (hom : ∀ {X Y}, (X ⟶ Y) → FC X Y)
  /-- Convert a bundled function to a morphism of `C`. -/
  (ofHom : ∀ {X Y}, FC X Y → (X ⟶ Y))
  (hom_ofHom : ∀ {X Y} (f : FC X Y), hom (ofHom f) = f := by cat_disch)
  (ofHom_hom : ∀ {X Y} (f : X ⟶ Y), ofHom (hom f) = f := by cat_disch)
  (id_apply : ∀ {X} (x : CC X), hom (𝟙 X) x = x := by cat_disch)
  (comp_apply : ∀ {X Y Z} (f : X ⟶ Y) (g : Y ⟶ Z) (x : CC X),
    hom (f ≫ g) x = hom g (hom f x) := by cat_disch)

attribute [simp] ConcreteCategory.hom_ofHom ConcreteCategory.ofHom_hom

variable {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type w}

variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
