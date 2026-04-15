/-
Extracted from AlgebraicGeometry/Modules/Sheaf.lean
Genuine: 6 of 17 | Dissolved: 0 | Infrastructure: 11
-/
import Origin.Core

/-!
# The category of sheaves of modules over a scheme

In this file, we define the abelian category of sheaves of modules
`X.Modules` over a scheme `X`, and study its basic functoriality.

-/

universe t u

open CategoryTheory Limits TopologicalSpace SheafOfModules Bicategory

namespace AlgebraicGeometry.Scheme

variable {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

variable (X) in

def Modules := SheafOfModules.{u} X.ringCatSheaf

namespace Modules

def Hom (M N : X.Modules) : Type u := SheafOfModules.Hom M N

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

section Functor

variable (X) in

def toPresheafOfModules : X.Modules ⥤ X.PresheafOfModules := SheafOfModules.forget _

def fullyFaithfulToPresheafOfModules : (Modules.toPresheafOfModules X).FullyFaithful :=
  SheafOfModules.fullyFaithfulForget _

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

variable (X) in

noncomputable def toPresheaf : X.Modules ⥤ TopCat.Presheaf Ab X :=
  toPresheafOfModules X ⋙ PresheafOfModules.toPresheaf _

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

end Functor

variable {M N K : X.Modules} {φ : M ⟶ N} {U V : X.Opens}

section Presheaf

noncomputable def presheaf (M : X.Modules) : TopCat.Presheaf Ab X := M.1.presheaf

scoped[AlgebraicGeometry] notation3 "Γ(" M ", " U ")" => (Scheme.Modules.presheaf M).obj (.op U)

-- INSTANCE (free from Core): :

variable (M) in
