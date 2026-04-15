/-
Extracted from CategoryTheory/Limits/Shapes/RegularMono.lean
Genuine: 6 of 6 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Definitions and basic properties of regular monomorphisms and epimorphisms.

A regular monomorphism is a morphism that is the equalizer of some parallel pair.

In this file, we give the following definitions.
* `RegularMono f`, which is a structure carrying the data that exhibits `f` as a regular
  monomorphism. That is, it carries a fork and data specifying `f` as the equalizer of that fork.
* `IsRegularMono f`, which is a `Prop`-valued class stating that `f` is a regular monomorphism. In
  particular, this doesn't carry any data.

and constructions
* `IsSplitMono f → RegularMono f` and
* `RegularMono f → Mono f`

as well as the dual definitions/constructions for regular epimorphisms.

Additionally, we give the constructions
* `RegularEpi f → EffectiveEpi f`, from which it can be deduced that regular epimorphisms are
  strong.
* `regularEpiOfEffectiveEpi`: constructs a `RegularEpi f` instance from `EffectiveEpi f` and
  `HasPullback f f`.

We also define classes `IsRegularMonoCategory` and `IsRegularEpiCategory` for categories in which
every monomorphism or epimorphism is regular, and deduce that these categories are
`StrongMonoCategory`s resp. `StrongEpiCategory`s.

-/

noncomputable section

namespace CategoryTheory

open CategoryTheory.Limits

universe v₁ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]

variable {X Y : C}

structure RegularMono (f : X ⟶ Y) where
  /-- An object in `C` -/
  Z : C
  /-- A map from the codomain of `f` to `Z` -/
  left : Y ⟶ Z
  /-- Another map from the codomain of `f` to `Z` -/
  right : Y ⟶ Z
  /-- `f` equalizes the two maps -/
  w : f ≫ left = f ≫ right := by cat_disch
  /-- `f` is the equalizer of the two maps -/
  isLimit : IsLimit (Fork.ofι f w)

attribute [reassoc] RegularMono.w

lemma RegularMono.mono {f : X ⟶ Y} (h : RegularMono f) : Mono f :=
  mono_of_isLimit_fork h.isLimit

def RegularMono.ofIso (e : X ≅ Y) : RegularMono e.hom where
  Z := Y
  left := 𝟙 Y
  right := 𝟙 Y
  isLimit := Fork.IsLimit.mk _ (fun s ↦ s.ι ≫ e.inv) (by simp) fun s m w ↦ by simp [← w]

set_option backward.isDefEq.respectTransparency false in

def RegularMono.ofArrowIso {X'} {Y'} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (e : Arrow.mk f ≅ Arrow.mk g) (h : RegularMono f) :
    RegularMono g where
  Z := h.Z
  left := e.inv.right ≫ h.left
  right := e.inv.right ≫ h.right
  w := by simp only [← (Arrow.w_mk_assoc e.inv), h.w]
  isLimit := Fork.isLimitOfIsos _ h.isLimit _
    (Arrow.rightFunc.mapIso e) (Iso.refl _) (Arrow.leftFunc.mapIso e)

class IsRegularMono {X Y : C} (f : X ⟶ Y) : Prop where
  regularMono : Nonempty (RegularMono f)

variable (C) in

def MorphismProperty.regularMono : MorphismProperty C := fun _ _ f => IsRegularMono f
