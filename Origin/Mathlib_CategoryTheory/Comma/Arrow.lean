/-
Extracted from CategoryTheory/Comma/Arrow.lean
Genuine: 7 of 8 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# The category of arrows

The category of arrows, with morphisms commutative squares.
We set this up as a specialization of the comma category `Comma L R`,
where `L` and `R` are both the identity functor.

## Tags

comma, arrow
-/

namespace CategoryTheory

universe v u

variable {T : Type u} [Category.{v} T]

variable (T) in

def Arrow := Comma (𝟭 T) (𝟭 T)

protected def Arrow.Hom (f g : Arrow T) := CommaMorphism f g

-- INSTANCE (free from Core): :

namespace Arrow

abbrev left (X : Arrow T) : T := Comma.left X

abbrev right (X : Arrow T) : T := Comma.right X

abbrev hom (X : Arrow T) : X.left ⟶ X.right := Comma.hom X

abbrev Hom.left {X Y : Arrow T} (f : X ⟶ Y) : X.left ⟶ Y.left := CommaMorphism.left f

abbrev Hom.right {X Y : Arrow T} (f : X ⟶ Y) : X.right ⟶ Y.right := CommaMorphism.right f
