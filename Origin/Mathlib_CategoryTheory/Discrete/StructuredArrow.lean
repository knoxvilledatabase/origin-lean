/-
Extracted from CategoryTheory/Discrete/StructuredArrow.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Structured arrows when the target category is discrete

When `T` is a type with a unique element `t`, we show that
if `F : C ⥤ Discrete T`, then the categories
`StructuredArrow (Discrete.mk t) F` and
`CostructuredArrow (Discrete.mk t) F` are equivalent to `C`.

-/

universe w v v' u u'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {T : Type w}

namespace Discrete

def structuredArrowEquivalenceOfUnique
    (F : C ⥤ Discrete T) (t : T) [Subsingleton T] :
    StructuredArrow (.mk t) F ≌ C where
  functor := StructuredArrow.proj _ _
  inverse.obj X := StructuredArrow.mk (Y := X) (eqToHom (by subsingleton))
  inverse.map f := StructuredArrow.homMk f
  unitIso := NatIso.ofComponents (fun _ ↦ StructuredArrow.isoMk (Iso.refl _))
  counitIso := Iso.refl _

def costructuredArrowEquivalenceOfUnique
    (F : C ⥤ Discrete T) (t : T) [Subsingleton T] :
    CostructuredArrow F (.mk t) ≌ C where
  functor := CostructuredArrow.proj _ _
  inverse.obj X := CostructuredArrow.mk (Y := X) (eqToHom (by subsingleton))
  inverse.map f := CostructuredArrow.homMk f
  unitIso := NatIso.ofComponents (fun _ ↦ CostructuredArrow.isoMk (Iso.refl _))
  counitIso := Iso.refl _

end Discrete

end CategoryTheory
