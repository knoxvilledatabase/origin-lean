/-
Extracted from CategoryTheory/Join/Final.lean
Genuine: 2 of 4 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# (Co)Finality of the inclusions in joins of categories

This file records the fact that `inclLeft C D : C ⥤ C ⋆ D` is initial if `C` is connected.
Dually, `inclRight : C ⥤ C ⋆ D` is final if `D` is connected.

-/

namespace CategoryTheory.Join

variable (C D : Type*) [Category* C] [Category* D]

def costructuredArrowEquiv (d : D) : CostructuredArrow (inclLeft C D) (right d) ≌ C where
  functor := CostructuredArrow.proj (inclLeft C D) (right d)
  inverse :=
    { obj c := .mk (edge c d)
      map f := CostructuredArrow.homMk f }
  unitIso := NatIso.ofComponents (fun _ ↦ CostructuredArrow.isoMk (Iso.refl _))
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _)

def structuredArrowEquiv (c : C) : StructuredArrow (left c) (inclRight C D) ≌ D where
  functor := StructuredArrow.proj (left c) (inclRight C D)
  inverse :=
    { obj d := .mk (edge c d)
      map f := StructuredArrow.homMk f }
  unitIso := NatIso.ofComponents (fun _ ↦ StructuredArrow.isoMk (Iso.refl _))
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _)

-- INSTANCE (free from Core): [IsConnected

-- INSTANCE (free from Core): [IsConnected

end CategoryTheory.Join
