/-
Extracted from CategoryTheory/Limits/IndYoneda.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Ind- and pro- (co)yoneda lemmas

We define limit versions of the yoneda and coyoneda lemmas.

## Main results

Notation: categories `C`, `I` and functors `D : Iᵒᵖ ⥤ C`, `F : C ⥤ Type`.

- `colimitCoyonedaHomIsoLimit`: pro-coyoneda lemma: morphisms from colimit of coyoneda of
  diagram `D` to `F` is limit of `F` evaluated at `D`.
- `colimitCoyonedaHomIsoLimit'`: a variant of `colimitCoyonedaHomIsoLimit` for a covariant
  diagram.

-/

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

namespace Limits

open Opposite

variable {C : Type u₁} [Category.{u₂} C] {I : Type v₁} [Category.{v₂} I]

section HomCocontinuousCovariant

variable (F : I ⥤ C) [HasColimit F]

noncomputable def coyonedaOpColimitIsoLimitCoyoneda :
    coyoneda.obj (op <| colimit F) ≅ limit (F.op ⋙ coyoneda) :=
  coyoneda.mapIso (limitOpIsoOpColimit F).symm ≪≫ (preservesLimitIso coyoneda F.op)

set_option backward.isDefEq.respectTransparency false in
