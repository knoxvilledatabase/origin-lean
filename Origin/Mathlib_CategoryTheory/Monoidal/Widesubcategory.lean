/-
Extracted from CategoryTheory/Monoidal/Widesubcategory.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Monoidal structures on wide subcategories

Given a monoidal category `C` and a morphism property `P : MorphismProperty C`,
this file introduces conditions on `P` ensuring that `WideSubcategory P` inherits
additional structures.

We define stability classes under associators, unitors, and braidings, and use
them to construct monoidal, braided, and symmetric structures on
`WideSubcategory P`.

-/

namespace CategoryTheory

open scoped MonoidalCategory ComonObj

variable {C : Type*} [Category* C] (P : MorphismProperty C) [MonoidalCategory C]

namespace MorphismProperty

class IsStableUnderAssociator (P : MorphismProperty C) : Prop where
  associator_hom_mem (P) (c c' c'' : C) : P (α_ c c' c'').hom
  associator_inv_mem (P) (c c' c'' : C) : P (α_ c c' c'').inv

export IsStableUnderAssociator (associator_hom_mem associator_inv_mem)

class IsStableUnderUnitor (P : MorphismProperty C) : Prop where
  leftUnitor_hom_mem (P) (c : C) : P ((λ_ c).hom)
  leftUnitor_inv_mem (P) (c : C) : P ((λ_ c).inv)
  rightUnitor_hom_mem (P) (c : C) : P ((ρ_ c).hom)
  rightUnitor_inv_mem (P) (c : C) : P ((ρ_ c).inv)

export IsStableUnderUnitor (leftUnitor_hom_mem leftUnitor_inv_mem rightUnitor_hom_mem

  rightUnitor_inv_mem)

class IsMonoidalStable : Prop extends IsMonoidal P, IsStableUnderAssociator P,
    IsStableUnderUnitor P

class IsStableUnderBraiding [BraidedCategory C] (P : MorphismProperty C) : Prop
    extends IsMonoidalStable P where
  braiding_hom_mem (P) (c c' : C) : P (β_ c c').hom
  braiding_inv_mem (P) (c c' : C) : P (β_ c c').inv

export IsStableUnderBraiding (braiding_hom_mem braiding_inv_mem)

end MorphismProperty

namespace WideSubcategory
