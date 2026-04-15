/-
Extracted from CategoryTheory/Bicategory/Monad/Basic.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Comonads in a bicategory

We define comonads in a bicategory `B` as comonoid objects in an endomorphism monoidal category.
We show that this is equivalent to oplax functors from the trivial bicategory to `B`. From this,
we show that comonads in `B` form a bicategory.

## TODO

We can also define monads in a bicategory. This is not yet done as we don't have the bicategory
structure on the set of lax functors at this point, which is needed to show that monads form a
bicategory.
-/

namespace CategoryTheory

namespace Bicategory

universe w v u

variable {B : Type u} [Bicategory.{w, v} B]

abbrev Comonad {a : B} (t : a ⟶ a) := ComonObj t

abbrev Comonad.counit {a : B} {t : a ⟶ a} [Comonad t] : t ⟶ 𝟙 a := ComonObj.counit

abbrev Comonad.comul {a : B} {t : a ⟶ a} [Comonad t] : t ⟶ t ≫ t := ComonObj.comul
