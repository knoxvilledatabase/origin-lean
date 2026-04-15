/-
Extracted from CategoryTheory/Sites/Sheafification.lean
Genuine: 7 of 15 | Dissolved: 0 | Infrastructure: 8
-/
import Origin.Core

/-!

# Sheafification

Given a site `(C, J)` we define a typeclass `HasSheafify J A` saying that the inclusion functor from
`A`-valued sheaves on `C` to presheaves admits a left exact left adjoint (sheafification).

Note: to access the `HasSheafify` instance for suitable concrete categories, import the file
`Mathlib/CategoryTheory/Sites/LeftExact.lean`.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)

variable (A : Type u₂) [Category.{v₂} A]

abbrev HasWeakSheafify : Prop := (sheafToPresheaf J A).IsRightAdjoint

class HasSheafify : Prop where
  isRightAdjoint : HasWeakSheafify J A
  isLeftExact : PreservesFiniteLimits ((sheafToPresheaf J A).leftAdjoint)

-- INSTANCE (free from Core): [HasSheafify

noncomputable section

-- INSTANCE (free from Core): [HasSheafify

theorem HasSheafify.mk' {F : (Cᵒᵖ ⥤ A) ⥤ Sheaf J A} (adj : F ⊣ sheafToPresheaf J A)
    [PreservesFiniteLimits F] : HasSheafify J A where
  isRightAdjoint := ⟨F, ⟨adj⟩⟩
  isLeftExact := ⟨by
    have : (sheafToPresheaf J A).IsRightAdjoint := ⟨_, ⟨adj⟩⟩
    exact fun _ _ _ ↦ preservesLimitsOfShape_of_natIso
      (adj.leftAdjointUniq (Adjunction.ofIsRightAdjoint (sheafToPresheaf J A)))⟩

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): {F

def presheafToSheaf [HasWeakSheafify J A] : (Cᵒᵖ ⥤ A) ⥤ Sheaf J A :=
  (sheafToPresheaf J A).leftAdjoint

-- INSTANCE (free from Core): [HasSheafify

def sheafificationAdjunction [HasWeakSheafify J A] :
    presheafToSheaf J A ⊣ sheafToPresheaf J A := Adjunction.ofIsRightAdjoint _

-- INSTANCE (free from Core): [HasWeakSheafify

-- INSTANCE (free from Core): [HasWeakSheafify

-- INSTANCE (free from Core): [HasSheafify

end

variable {D : Type*} [Category* D] [HasWeakSheafify J D]

noncomputable abbrev sheafify (P : Cᵒᵖ ⥤ D) : Cᵒᵖ ⥤ D :=
  presheafToSheaf J D |>.obj P |>.obj

noncomputable abbrev toSheafify (P : Cᵒᵖ ⥤ D) : P ⟶ sheafify J P :=
  sheafificationAdjunction J D |>.unit.app P
