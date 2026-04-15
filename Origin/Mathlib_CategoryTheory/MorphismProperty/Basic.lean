/-
Extracted from CategoryTheory/MorphismProperty/Basic.lean
Genuine: 1 of 5 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Properties of morphisms

We provide the basic framework for talking about properties of morphisms.
The following meta-property is defined

* `RespectsLeft P Q`: `P` respects the property `Q` on the left if `P f → P (i ≫ f)` where
  `i` satisfies `Q`.
* `RespectsRight P Q`: `P` respects the property `Q` on the right if `P f → P (f ≫ i)` where
  `i` satisfies `Q`.
* `Respects`: `P` respects `Q` if `P` respects `Q` both on the left and on the right.

-/

universe w v v' u u'

open CategoryTheory Opposite

noncomputable section

namespace CategoryTheory

def MorphismProperty (C : Type u) [CategoryStruct.{v} C] :=
  ∀ ⦃X Y : C⦄ (_ : X ⟶ Y), Prop

namespace MorphismProperty

variable (C : Type u) [CategoryStruct.{v} C]

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

variable {C}
