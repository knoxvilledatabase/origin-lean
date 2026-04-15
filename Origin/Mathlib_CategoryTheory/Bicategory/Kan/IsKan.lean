/-
Extracted from CategoryTheory/Bicategory/Kan/IsKan.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Kan extensions and Kan lifts in bicategories

The left Kan extension of a 1-morphism `g : a ⟶ c` along a 1-morphism `f : a ⟶ b` is the initial
object in the category of left extensions `LeftExtension f g`. The universal property can be
accessed by the following definition and lemmas:
* `LeftExtension.IsKan.desc`: the family of 2-morphisms out of the left Kan extension.
* `LeftExtension.IsKan.fac`: the unit of any left extension factors through the left Kan extension.
* `LeftExtension.IsKan.hom_ext`: two 2-morphisms out of the left Kan extension are equal if their
  compositions with each unit are equal.

We also define left Kan lifts, right Kan extensions, and right Kan lifts.

## Implementation Notes

We use the Is-Has design pattern, which is used for the implementation of limits and colimits in
the category theory library. This means that `IsKan t` is a structure containing the data of
2-morphisms which ensure that `t` is a Kan extension, while `HasLeftKanExtension f g`
(and similarly for lifts) defined in `CategoryTheory.Bicategory.Kan.HasKan`
is a `Prop`-valued typeclass asserting that a Kan extension of `g` along `f` exists.

We define `LeftExtension.IsKan t` for an extension `t : LeftExtension f g` (which is an
abbreviation of `t : StructuredArrow g (precomp _ f)`) to be an abbreviation for
`StructuredArrow.IsUniversal t`. This means that we can use the definitions and lemmas living
in the namespace `StructuredArrow.IsUniversal`.

## References
https://ncatlab.org/nlab/show/Kan+extension

-/

namespace CategoryTheory

namespace Bicategory

universe w v u

variable {B : Type u} [Bicategory.{w, v} B] {a b c : B}

namespace LeftExtension

variable {f : a ⟶ b} {g : a ⟶ c}

abbrev IsKan (t : LeftExtension f g) := t.IsUniversal

abbrev IsAbsKan (t : LeftExtension f g) :=
  ∀ {x : B} (h : c ⟶ x), IsKan (t.whisker h)

namespace IsKan

variable {s t : LeftExtension f g}

abbrev mk (desc : ∀ s, t ⟶ s) (w : ∀ s τ, τ = desc s) :
    IsKan t :=
  .ofUniqueHom desc w

abbrev desc (H : IsKan t) (s : LeftExtension f g) : t.extension ⟶ s.extension :=
  StructuredArrow.IsUniversal.desc H s
