/-
Extracted from CategoryTheory/Limits/Types/Coproducts.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Coproducts in `Type`

If `F : J → Type max v u` (with `J : Type v`), we show that the coproduct
of `F` exists in `Type max v u` and identifies to the sigma type `Σ j, F j`.
Similarly, the binary coproduct of two types `X` and `Y` identifies to
`X ⊕ Y`, and the initial object of `Type u` if `PEmpty`.

-/

universe w v u

namespace CategoryTheory

namespace Limits

variable {C : Type u} (F : C → Type v)

abbrev CofanTypes := Functor.CoconeTypes.{w} (Discrete.functor F)

variable {F}

namespace CofanTypes

abbrev inj (c : CofanTypes.{w} F) (i : C) : F i → c.pt := c.ι ⟨i⟩

variable (F) in
