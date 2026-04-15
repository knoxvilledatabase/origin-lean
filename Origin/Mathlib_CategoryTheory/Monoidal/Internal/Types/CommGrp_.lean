/-
Extracted from CategoryTheory/Monoidal/Internal/Types/CommGrp_.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# `CommGrp (Type u) ≌ CommGrpCat.{u}`

The category of internal commutative group objects in `Type`
is equivalent to the category of "native" bundled commutative groups.

Moreover, this equivalence is compatible with the forgetful functors to `Type`.
-/

assert_not_exists Field

universe v u

open CategoryTheory MonObj ConcreteCategory

namespace CommGrpTypeEquivalenceCommGrp

-- INSTANCE (free from Core): commGrpCommGroup

noncomputable def functor : CommGrp (Type u) ⥤ CommGrpCat.{u} where
  obj A := CommGrpCat.of A.X
  map f := CommGrpCat.ofHom (GrpTypeEquivalenceGrp.functor.map f.hom).hom

noncomputable def inverse : CommGrpCat.{u} ⥤ CommGrp (Type u) where
  obj A :=
    { grpTypeEquivalenceGrp.inverse.obj ((forget₂ CommGrpCat GrpCat).obj A) with
      comm :=
        { mul_comm := by
            ext ⟨x : A, y : A⟩
            exact CommMonoid.mul_comm y x } }
  map f := InducedCategory.homMk
    (GrpTypeEquivalenceGrp.inverse.map ((forget₂ CommGrpCat GrpCat).map f))
