/-
Extracted from Topology/Category/Profinite/AsLimit.lean
Genuine: 7 of 8 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Profinite sets as limits of finite sets.

We show that any profinite set is isomorphic to the limit of its
discrete (hence finite) quotients.

## Definitions

There are a handful of definitions in this file, given `X : Profinite`:
1. `X.fintypeDiagram` is the functor `DiscreteQuotient X ⥤ FintypeCat` whose limit
  is isomorphic to `X` (the limit taking place in `Profinite` via `FintypeCat.toProfinite`, see 2).
2. `X.diagram` is an abbreviation for `X.fintypeDiagram ⋙ FintypeCat.toProfinite`.
3. `X.asLimitCone` is the cone over `X.diagram` whose cone point is `X`.
4. `X.isoAsLimitConeLift` is the isomorphism `X ≅ (Profinite.limitCone X.diagram).X` induced
  by lifting `X.asLimitCone`.
5. `X.asLimitConeIso` is the isomorphism `X.asLimitCone ≅ (Profinite.limitCone X.diagram)`
  induced by `X.isoAsLimitConeLift`.
6. `X.asLimit` is a term of type `IsLimit X.asLimitCone`.
7. `X.lim : CategoryTheory.Limits.LimitCone X.asLimitCone` is a bundled combination of 3 and 6.

-/

noncomputable section

open CategoryTheory

namespace Profinite

universe u

variable (X : Profinite.{u})

def fintypeDiagram : DiscreteQuotient X ⥤ FintypeCat where
  obj S := FintypeCat.of S
  map f := FintypeCat.homMk (DiscreteQuotient.ofLE f.le)

abbrev diagram : DiscreteQuotient X ⥤ Profinite :=
  X.fintypeDiagram ⋙ FintypeCat.toProfinite

def asLimitCone : CategoryTheory.Limits.Cone X.diagram :=
  { pt := X
    π := { app := fun S => CompHausLike.ofHom (Y := X.diagram.obj S) _
            ⟨S.proj, IsLocallyConstant.continuous (S.proj_isLocallyConstant)⟩ } }

-- INSTANCE (free from Core): isIso_asLimitCone_lift

set_option backward.isDefEq.respectTransparency false in

def isoAsLimitConeLift : X ≅ (limitCone.{u, u} X.diagram).pt :=
  asIso <| (limitConeIsLimit.{u, u} _).lift X.asLimitCone

def asLimitConeIso : X.asLimitCone ≅ limitCone.{u, u} _ :=
  Limits.Cone.ext (isoAsLimitConeLift _) fun _ => rfl

def asLimit : CategoryTheory.Limits.IsLimit X.asLimitCone :=
  Limits.IsLimit.ofIsoLimit (limitConeIsLimit _) X.asLimitConeIso.symm

def lim : Limits.LimitCone X.diagram :=
  ⟨X.asLimitCone, X.asLimit⟩

end Profinite
