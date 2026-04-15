/-
Extracted from Algebra/Category/Grp/EquivalenceGroupAddGroup.lean
Genuine: 6 of 10 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core
import Mathlib.Algebra.Category.Grp.Basic

/-!
# Equivalence between `Group` and `AddGroup`

This file contains two equivalences:
* `groupAddGroupEquivalence` : the equivalence between `Grp` and `AddGrp` by sending
  `X : Grp` to `Additive X` and `Y : AddGrp` to `Multiplicative Y`.
* `commGroupAddCommGroupEquivalence` : the equivalence between `CommGrp` and `AddCommGrp`
  by sending `X : CommGrp` to `Additive X` and `Y : AddCommGrp` to `Multiplicative Y`.
-/

open CategoryTheory

namespace Grp

private instance (X : Grp) : MulOneClass X.α := X.str.toMulOneClass

private instance (X : CommGrp) : MulOneClass X.α := X.str.toMulOneClass

private instance (X : AddGrp) : AddZeroClass X.α := X.str.toAddZeroClass

private instance (X : AddCommGrp) : AddZeroClass X.α := X.str.toAddZeroClass

@[simps]
def toAddGrp : Grp ⥤ AddGrp where
  obj X := AddGrp.of (Additive X)
  map {_} {_} := MonoidHom.toAdditive

end Grp

namespace CommGrp

@[simps]
def toAddCommGrp : CommGrp ⥤ AddCommGrp where
  obj X := AddCommGrp.of (Additive X)
  map {_} {_} := MonoidHom.toAdditive

end CommGrp

namespace AddGrp

@[simps]
def toGrp : AddGrp ⥤ Grp where
  obj X := Grp.of (Multiplicative X)
  map {_} {_} := AddMonoidHom.toMultiplicative

end AddGrp

namespace AddCommGrp

@[simps]
def toCommGrp : AddCommGrp ⥤ CommGrp where
  obj X := CommGrp.of (Multiplicative X)
  map {_} {_} := AddMonoidHom.toMultiplicative

end AddCommGrp

@[simps]
def groupAddGroupEquivalence : Grp ≌ AddGrp where
  functor := Grp.toAddGrp
  inverse := AddGrp.toGrp
  unitIso := Iso.refl _
  counitIso := Iso.refl _

@[simps]
def commGroupAddCommGroupEquivalence : CommGrp ≌ AddCommGrp where
  functor := CommGrp.toAddCommGrp
  inverse := AddCommGrp.toCommGrp
  unitIso := Iso.refl _
  counitIso := Iso.refl _
