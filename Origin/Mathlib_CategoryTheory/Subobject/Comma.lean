/-
Extracted from CategoryTheory/Subobject/Comma.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Subobjects in the category of structured arrows

We compute the subobjects of an object `A` in the category `StructuredArrow S T` for `T : C ⥤ D`
and `S : D` as a subtype of the subobjects of `A.right`. We deduce that `StructuredArrow S T` is
well-powered if `C` is.

## Main declarations
* `StructuredArrow.subobjectEquiv`: the order-equivalence between `Subobject A` and a subtype of
  `Subobject A.right`.

## Implementation notes
Our computation requires that `C` has all limits and `T` preserves all limits. Furthermore, we
require that the morphisms of `C` and `D` are in the same universe. It is possible that both of
these requirements can be relaxed by refining the results about limits in comma categories.

We also provide the dual results. As usual, we use `Subobject (op A)` for the quotient objects of
`A`.

-/

noncomputable section

open CategoryTheory.Limits Opposite

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace StructuredArrow

variable {S : D} {T : C ⥤ D}

def projectSubobject [HasFiniteLimits C] [PreservesFiniteLimits T] {A : StructuredArrow S T} :
    Subobject A → Subobject A.right := by
  refine Subobject.lift (fun P f hf => Subobject.mk f.right) ?_
  intro P Q f g hf hg i hi
  refine Subobject.mk_eq_mk_of_comm _ _ ((proj S T).mapIso i) ?_
  exact congr_arg CommaMorphism.right hi
