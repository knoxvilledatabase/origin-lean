/-
Extracted from CategoryTheory/Idempotents/FunctorExtension.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Extension of functors to the idempotent completion

In this file, we construct an extension `functorExtension₁`
of functors `C ⥤ Karoubi D` to functors `Karoubi C ⥤ Karoubi D`. This results in an
equivalence `karoubiUniversal₁ C D : (C ⥤ Karoubi D) ≌ (Karoubi C ⥤ Karoubi D)`.

We also construct an extension `functorExtension₂` of functors
`(C ⥤ D) ⥤ (Karoubi C ⥤ Karoubi D)`. Moreover,
when `D` is idempotent complete, we get equivalences
`karoubiUniversal₂ C D : C ⥤ D ≌ Karoubi C ⥤ Karoubi D`
and `karoubiUniversal C D : C ⥤ D ≌ Karoubi C ⥤ D`.

-/

namespace CategoryTheory

namespace Idempotents

open Category Karoubi Functor

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]

theorem natTrans_eq {F G : Karoubi C ⥤ D} (φ : F ⟶ G) (P : Karoubi C) :
    φ.app P = F.map (decompId_i P) ≫ φ.app P.X ≫ G.map (decompId_p P) := by
  rw [← φ.naturality, ← assoc, ← F.map_comp]
  conv_lhs => rw [← id_comp (φ.app P), ← F.map_id]
  congr
  apply decompId

namespace FunctorExtension₁
