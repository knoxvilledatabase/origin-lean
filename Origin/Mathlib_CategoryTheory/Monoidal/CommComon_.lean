/-
Extracted from CategoryTheory/Monoidal/CommComon_.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The category of commutative comonoids in a braided monoidal category.

We define the category of commutative comonoid objects in a braided monoidal category `C`.

## Main definitions

* `CommComon C` - The bundled structure of commutative comonoid objects

## Tags

comonoid, commutative, braided
-/

universe v₁ v₂ v₃ u₁ u₂ u₃ u

namespace CategoryTheory

open MonoidalCategory ComonObj Functor

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C] [BraidedCategory.{v₁} C]

variable (C) in

structure CommComon where
  /-- The underlying object in the ambient monoidal category -/
  X : C
  [comon : ComonObj X]
  [comm : IsCommComonObj X]

attribute [instance] CommComon.comon CommComon.comm

namespace CommComon
