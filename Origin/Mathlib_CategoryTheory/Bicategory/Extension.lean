/-
Extracted from CategoryTheory/Bicategory/Extension.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Extensions and lifts in bicategories

We introduce the concept of extensions and lifts within the bicategorical framework. These concepts
are defined by commutative diagrams in the (1-)categorical context. Within the bicategorical
framework, commutative diagrams are replaced by 2-morphisms. Depending on the orientation of the
2-morphisms, we define both left and right extensions (likewise for lifts). The use of left and
right here is a common one in the theory of Kan extensions.

## Implementation notes
We define extensions and lifts as objects in certain comma categories (`StructuredArrow` for left,
and `CostructuredArrow` for right). See the file `CategoryTheory.StructuredArrow` for properties
about these categories. We introduce some intuitive aliases. For example, `LeftExtension.extension`
is an alias for `Comma.right`.

## References
* https://ncatlab.org/nlab/show/lifts+and+extensions
* https://ncatlab.org/nlab/show/Kan+extension

-/

namespace CategoryTheory

namespace Bicategory

universe w v u

variable {B : Type u} [Bicategory.{w, v} B] {a b c : B}

abbrev LeftExtension (f : a ⟶ b) (g : a ⟶ c) := StructuredArrow g (precomp _ f)

namespace LeftExtension

variable {f : a ⟶ b} {g : a ⟶ c}

abbrev extension (t : LeftExtension f g) : b ⟶ c := t.right

abbrev unit (t : LeftExtension f g) : g ⟶ f ≫ t.extension := t.hom

abbrev mk (h : b ⟶ c) (unit : g ⟶ f ≫ h) : LeftExtension f g :=
  StructuredArrow.mk unit

variable {s t : LeftExtension f g}

abbrev homMk (η : s.extension ⟶ t.extension) (w : s.unit ≫ f ◁ η = t.unit := by cat_disch) :
    s ⟶ t :=
  StructuredArrow.homMk η w
