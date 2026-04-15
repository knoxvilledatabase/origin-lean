/-
Extracted from AlgebraicTopology/ModelCategory/Bifibrant.lean
Genuine: 6 of 6 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Bifibrant objects

In this file, we introduce the full subcategories `CofibrantObject C`,
`FibrantObject C` and `BifibrantObject C` of a model category `C` which
respectively consist of cofibrant objects, fibrant objects,
and bifibrant objects, where "bifibrant" means both cofibrant and fibrant.

-/

universe v u

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C]

section Cofibrant

variable [CategoryWithCofibrations C] [HasInitial C]

variable (C) in

def cofibrantObjects : ObjectProperty C := IsCofibrant

variable (C) in

abbrev CofibrantObject : Type u := (cofibrantObjects C).FullSubcategory

namespace CofibrantObject

abbrev mk (X : C) [IsCofibrant X] : CofibrantObject C :=
  ⟨X, by assumption⟩

lemma mk_surjective (X : CofibrantObject C) :
    ∃ (Y : C) (_ : IsCofibrant Y), X = mk Y := ⟨X.obj, X.property, rfl⟩

abbrev homMk {X Y : C} [IsCofibrant X] [IsCofibrant Y] (f : X ⟶ Y) :
    mk X ⟶ mk Y := ObjectProperty.homMk f

lemma homMk_surjective {X Y : C} [IsCofibrant X] [IsCofibrant Y]
    (f : mk X ⟶ mk Y) :
    ∃ (g : X ⟶ Y), f = homMk g := ⟨f.hom, rfl⟩
