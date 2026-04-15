/-
Extracted from CategoryTheory/Monoidal/Free/Basic.lean
Genuine: 3 of 6 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# The free monoidal category over a type

Given a type `C`, the free monoidal category over `C` has as objects formal expressions built from
(formal) tensor products of terms of `C` and a formal unit. Its morphisms are compositions and
tensor products of identities, unitors and associators.

In this file, we construct the free monoidal category and prove that it is a monoidal category. If
`D` is a monoidal category, we construct the functor `FreeMonoidalCategory C ⥤ D` associated to
a function `C → D`.

The free monoidal category has two important properties: it is a groupoid and it is thin. The former
is obvious from the construction, and the latter is what is commonly known as the monoidal coherence
theorem. Both of these properties are proved in the file `Coherence.lean`.

-/

universe v' u u'

namespace CategoryTheory

open MonoidalCategory

variable {C : Type u}

variable (C)

set_option genSizeOfSpec false in

set_option genInjectivity false in

inductive FreeMonoidalCategory : Type u
  | of : C → FreeMonoidalCategory
  | unit : FreeMonoidalCategory
  | tensor : FreeMonoidalCategory → FreeMonoidalCategory → FreeMonoidalCategory
  deriving Inhabited

end

local notation "F" => FreeMonoidalCategory

namespace FreeMonoidalCategory

inductive Hom : F C → F C → Type u
  | id (X) : Hom X X
  | α_hom (X Y Z : F C) : Hom ((X.tensor Y).tensor Z) (X.tensor (Y.tensor Z))
  | α_inv (X Y Z : F C) : Hom (X.tensor (Y.tensor Z)) ((X.tensor Y).tensor Z)
  | l_hom (X) : Hom (unit.tensor X) X
  | l_inv (X) : Hom X (unit.tensor X)
  | ρ_hom (X : F C) : Hom (X.tensor unit) X
  | ρ_inv (X : F C) : Hom X (X.tensor unit)
  | comp {X Y Z} (f : Hom X Y) (g : Hom Y Z) : Hom X Z
  | whiskerLeft (X : F C) {Y₁ Y₂} (f : Hom Y₁ Y₂) : Hom (X.tensor Y₁) (X.tensor Y₂)
  | whiskerRight {X₁ X₂} (f : Hom X₁ X₂) (Y : F C) : Hom (X₁.tensor Y) (X₂.tensor Y)
  | tensor {W X Y Z} (f : Hom W Y) (g : Hom X Z) : Hom (W.tensor X) (Y.tensor Z)

local infixr:10 " ⟶ᵐ " => Hom

inductive HomEquiv : ∀ {X Y : F C}, (X ⟶ᵐ Y) → (X ⟶ᵐ Y) → Prop
  | refl {X Y} (f : X ⟶ᵐ Y) : HomEquiv f f
  | symm {X Y} (f g : X ⟶ᵐ Y) : HomEquiv f g → HomEquiv g f
  | trans {X Y} {f g h : X ⟶ᵐ Y} : HomEquiv f g → HomEquiv g h → HomEquiv f h
  | comp {X Y Z} {f f' : X ⟶ᵐ Y} {g g' : Y ⟶ᵐ Z} :
      HomEquiv f f' → HomEquiv g g' → HomEquiv (f.comp g) (f'.comp g')
  | whiskerLeft (X) {Y Z} (f f' : Y ⟶ᵐ Z) :
      HomEquiv f f' → HomEquiv (f.whiskerLeft X) (f'.whiskerLeft X)
  | whiskerRight {Y Z} (f f' : Y ⟶ᵐ Z) (X) :
      HomEquiv f f' → HomEquiv (f.whiskerRight X) (f'.whiskerRight X)
  | tensor {W X Y Z} {f f' : W ⟶ᵐ X} {g g' : Y ⟶ᵐ Z} :
      HomEquiv f f' → HomEquiv g g' → HomEquiv (f.tensor g) (f'.tensor g')
  | tensorHom_def {X₁ Y₁ X₂ Y₂} (f : X₁ ⟶ᵐ Y₁) (g : X₂ ⟶ᵐ Y₂) :
      HomEquiv (f.tensor g) ((f.whiskerRight X₂).comp (g.whiskerLeft Y₁))
  | comp_id {X Y} (f : X ⟶ᵐ Y) : HomEquiv (f.comp (Hom.id _)) f
  | id_comp {X Y} (f : X ⟶ᵐ Y) : HomEquiv ((Hom.id _).comp f) f
  | assoc {X Y U V : F C} (f : X ⟶ᵐ U) (g : U ⟶ᵐ V) (h : V ⟶ᵐ Y) :
      HomEquiv ((f.comp g).comp h) (f.comp (g.comp h))
  | id_tensorHom_id {X Y} : HomEquiv ((Hom.id X).tensor (Hom.id Y)) (Hom.id _)
  | tensorHom_comp_tensorHom {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : F C} (f₁ : X₁ ⟶ᵐ Y₁) (f₂ : X₂ ⟶ᵐ Y₂)
      (g₁ : Y₁ ⟶ᵐ Z₁) (g₂ : Y₂ ⟶ᵐ Z₂) :
    HomEquiv ((f₁.tensor f₂).comp (g₁.tensor g₂)) ((f₁.comp g₁).tensor (f₂.comp g₂))
  | whiskerLeft_id (X Y) : HomEquiv ((Hom.id Y).whiskerLeft X) (Hom.id (X.tensor Y))
  | id_whiskerRight (X Y) : HomEquiv ((Hom.id X).whiskerRight Y) (Hom.id (X.tensor Y))
  | α_hom_inv {X Y Z} : HomEquiv ((Hom.α_hom X Y Z).comp (Hom.α_inv X Y Z)) (Hom.id _)
  | α_inv_hom {X Y Z} : HomEquiv ((Hom.α_inv X Y Z).comp (Hom.α_hom X Y Z)) (Hom.id _)
  | associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃} (f₁ : X₁ ⟶ᵐ Y₁) (f₂ : X₂ ⟶ᵐ Y₂) (f₃ : X₃ ⟶ᵐ Y₃) :
      HomEquiv (((f₁.tensor f₂).tensor f₃).comp (Hom.α_hom Y₁ Y₂ Y₃))
        ((Hom.α_hom X₁ X₂ X₃).comp (f₁.tensor (f₂.tensor f₃)))
  | ρ_hom_inv {X} : HomEquiv ((Hom.ρ_hom X).comp (Hom.ρ_inv X)) (Hom.id _)
  | ρ_inv_hom {X} : HomEquiv ((Hom.ρ_inv X).comp (Hom.ρ_hom X)) (Hom.id _)
  | ρ_naturality {X Y} (f : X ⟶ᵐ Y) :
      HomEquiv ((f.whiskerRight unit).comp (Hom.ρ_hom Y)) ((Hom.ρ_hom X).comp f)
  | l_hom_inv {X} : HomEquiv ((Hom.l_hom X).comp (Hom.l_inv X)) (Hom.id _)
  | l_inv_hom {X} : HomEquiv ((Hom.l_inv X).comp (Hom.l_hom X)) (Hom.id _)
  | l_naturality {X Y} (f : X ⟶ᵐ Y) :
      HomEquiv ((f.whiskerLeft unit).comp (Hom.l_hom Y)) ((Hom.l_hom X).comp f)
  | pentagon {W X Y Z} :
      HomEquiv
        (((Hom.α_hom W X Y).whiskerRight Z).comp
          ((Hom.α_hom W (X.tensor Y) Z).comp ((Hom.α_hom X Y Z).whiskerLeft W)))
        ((Hom.α_hom (W.tensor X) Y Z).comp (Hom.α_hom W X (Y.tensor Z)))
  | triangle {X Y} :
      HomEquiv ((Hom.α_hom X unit Y).comp ((Hom.l_hom Y).whiskerLeft X))
        ((Hom.ρ_hom X).whiskerRight Y)

-- INSTANCE (free from Core): setoidHom

open FreeMonoidalCategory.HomEquiv

-- INSTANCE (free from Core): categoryFreeMonoidalCategory

-- INSTANCE (free from Core): :
