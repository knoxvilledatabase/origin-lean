/-
Extracted from CategoryTheory/Triangulated/TStructure/Heart.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The heart of a t-structure

Let `t` be a t-structure on a triangulated category `C`. We define
the heart of `t` as a property `t.heart : ObjectProperty C`. As the
the heart is usually identified to a particular category in the applications
(e.g. the heart of the canonical t-structure on the derived category of
an abelian category `A` identifies to `A`), instead of working
with the full subcategory defined by `t.heart`, we introduce a typeclass
`t.Heart H` which says that the additive category `H` identifies to
the full subcategory `t.heart`.

## TODO (@joelriou)
* Show that the heart is an abelian category.

## References
* [Beilinson, Bernstein, Deligne, Gabber, *Faisceaux pervers*][bbd-1982]

-/

universe v' u' v u

namespace CategoryTheory.Triangulated.TStructure

open Pretriangulated Limits

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
  (t : TStructure C)

def heart : ObjectProperty C := t.le 0 ⊓ t.ge 0
  deriving ObjectProperty.IsClosedUnderIsomorphisms

lemma mem_heart_iff (X : C) :
    t.heart X ↔ t.IsLE X 0 ∧ t.IsGE X 0 := by
  simp [heart]

variable (H : Type u') [Category.{v'} H] [Preadditive H]

class Heart where
  /-- The inclusion functor. -/
  ι : H ⥤ C
  additive_ι : ι.Additive := by infer_instance
  full_ι : ι.Full := by infer_instance
  faithful_ι : ι.Faithful := by infer_instance
  essImage_eq_heart : ι.essImage = t.heart := by simp
