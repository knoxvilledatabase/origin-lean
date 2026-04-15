/-
Extracted from CategoryTheory/Limits/Shapes/Images.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Categorical images

We define the categorical image of `f` as a factorisation `f = e ≫ m` through a monomorphism `m`,
so that `m` factors through the `m'` in any other such factorisation.

## Main definitions

* A `MonoFactorisation` is a factorisation `f = e ≫ m`, where `m` is a monomorphism
* `IsImage F` means that a given mono factorisation `F` has the universal property of the image.
* `HasImage f` means that there is some image factorization for the morphism `f : X ⟶ Y`.
  * In this case, `image f` is some image object (selected with choice), `image.ι f : image f ⟶ Y`
    is the monomorphism `m` of the factorisation and `factorThruImage f : X ⟶ image f` is the
    morphism `e`.
* `HasImages C` means that every morphism in `C` has an image.
* Let `f : X ⟶ Y` and `g : P ⟶ Q` be morphisms in `C`, which we will represent as objects of the
  arrow category `Arrow C`. Then `sq : f ⟶ g` is a commutative square in `C`. If `f` and `g` have
  images, then `HasImageMap sq` represents the fact that there is a morphism
  `i : image f ⟶ image g` making the diagram

  X ----→ image f ----→ Y
  |         |           |
  |         |           |
  ↓         ↓           ↓
  P ----→ image g ----→ Q

  commute, where the top row is the image factorisation of `f`, the bottom row is the image
  factorisation of `g`, and the outer rectangle is the commutative square `sq`.
* If a category `HasImages`, then `HasImageMaps` means that every commutative square admits an
  image map.
* If a category `HasImages`, then `HasStrongEpiImages` means that the morphism to the image is
  always a strong epimorphism.

## Main statements

* When `C` has equalizers, the morphism `e` appearing in an image factorisation is an epimorphism.
* When `C` has strong epi images, then these images admit image maps.

## Future work
* TODO: coimages, and abelian categories.
* TODO: connect this with existing work in the group theory and ring theory libraries.

-/

noncomputable section

universe w v u

open CategoryTheory

open CategoryTheory.Limits.WalkingParallelPair

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

variable {X Y : C} (f : X ⟶ Y)

structure MonoFactorisation (f : X ⟶ Y) where
  I : C
  m : I ⟶ Y
  [m_mono : Mono m]
  e : X ⟶ I
  fac : e ≫ m = f := by cat_disch

attribute [inherit_doc MonoFactorisation] MonoFactorisation.I MonoFactorisation.m

  MonoFactorisation.m_mono MonoFactorisation.e MonoFactorisation.fac

attribute [reassoc (attr := simp)] MonoFactorisation.fac

attribute [instance] MonoFactorisation.m_mono

namespace MonoFactorisation

def self [Mono f] : MonoFactorisation f where
  I := X
  m := f
  e := 𝟙 X

-- INSTANCE (free from Core): [Mono

variable {f}
