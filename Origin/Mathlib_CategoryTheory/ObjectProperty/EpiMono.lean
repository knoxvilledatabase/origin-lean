/-
Extracted from CategoryTheory/ObjectProperty/EpiMono.lean
Genuine: 6 of 14 | Dissolved: 0 | Infrastructure: 8
-/
import Origin.Core

/-!
# Properties of objects that are closed under subobjects and quotients

Given a category `C` and `P : ObjectProperty C`, we define type classes
`P.IsClosedUnderSubobjects` and `P.IsClosedUnderQuotients` expressing
that `P` is closed under subobjects (resp. quotients).

-/

universe v v' u u'

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

namespace ObjectProperty

variable (P : ObjectProperty C)

class IsClosedUnderSubobjects : Prop where
  prop_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] (hY : P Y) : P X

variable [P.IsClosedUnderSubobjects]

lemma prop_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] (hY : P Y) : P X :=
  IsClosedUnderSubobjects.prop_of_mono f hY

-- INSTANCE (free from Core): :

lemma prop_X₁_of_shortExact [HasZeroMorphisms C] {S : ShortComplex C} (hS : S.ShortExact)
    (h₂ : P S.X₂) : P S.X₁ := by
  have := hS.mono_f
  exact P.prop_of_mono S.f h₂

-- INSTANCE (free from Core): (F

end

class IsClosedUnderQuotients : Prop where
  prop_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] (hX : P X) : P Y

variable [P.IsClosedUnderQuotients]

lemma prop_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] (hX : P X) : P Y :=
  IsClosedUnderQuotients.prop_of_epi f hX

-- INSTANCE (free from Core): :

lemma prop_X₃_of_shortExact [HasZeroMorphisms C] {S : ShortComplex C} (hS : S.ShortExact)
    (h₂ : P S.X₂) : P S.X₃ := by
  have := hS.epi_g
  exact P.prop_of_epi S.g h₂

-- INSTANCE (free from Core): (F

end

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): [HasZeroMorphisms

-- INSTANCE (free from Core): [HasZeroMorphisms

end ObjectProperty

end CategoryTheory
