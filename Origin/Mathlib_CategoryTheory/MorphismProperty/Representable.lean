/-
Extracted from CategoryTheory/MorphismProperty/Representable.lean
Genuine: 7 of 7 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Relatively representable morphisms

In this file we define and develop basic results about relatively representable morphisms.

Classically, a morphism `f : F ⟶ G` of presheaves is said to be representable if for any morphism
`g : yoneda.obj X ⟶ G`, there exists a pullback square of the following form
```
  yoneda.obj Y --yoneda.map snd--> yoneda.obj X
      |                                |
     fst                               g
      |                                |
      v                                v
      F ------------ f --------------> G
```

In this file, we define a notion of relative representability which works with respect to any
functor, and not just `yoneda`. The fact that a morphism `f : F ⟶ G` between presheaves is
representable in the classical case will then be given by `yoneda.relativelyRepresentable f`.

## Main definitions

Throughout this file, `F : C ⥤ D` is a functor between categories `C` and `D`.

* `Functor.relativelyRepresentable`: A morphism `f : X ⟶ Y` in `D` is said to be relatively
  representable with respect to `F`, if for any `g : F.obj a ⟶ Y`, there exists a pullback square
  of the following form
  ```
  F.obj b --F.map snd--> F.obj a
      |                     |
     fst                    g
      |                     |
      v                     v
      X ------- f --------> Y
  ```

* `MorphismProperty.relative`: Given a morphism property `P` in `C`, a morphism `f : X ⟶ Y` in `D`
  satisfies `P.relative F` if it is relatively representable and for any `g : F.obj a ⟶ Y`, the
  property `P` holds for any represented pullback of `f` by `g`.

## API

Given `hf : relativelyRepresentable f`, with `f : X ⟶ Y` and `g : F.obj a ⟶ Y`, we provide:
* `hf.pullback g` which is the object in `C` such that `F.obj (hf.pullback g)` is a
  pullback of `f` and `g`.
* `hf.snd g` is the morphism `hf.pullback g ⟶ F.obj a`
* `hf.fst g` is the morphism `F.obj (hf.pullback g) ⟶ X`
* If `F` is full, and `f` is of type `F.obj c ⟶ G`, we also have `hf.fst' g : hf.pullback g ⟶ X`
  which is the preimage under `F` of `hf.fst g`.
* `hom_ext`, `hom_ext'`, `lift`, `lift'` are variants of the universal property of
  `F.obj (hf.pullback g)`, where as much as possible has been formulated internally to `C`.
  For these theorems we also need that `F` is full and/or faithful.
* `symmetry` and `symmetryIso` are variants of the fact that pullbacks are symmetric for
  representable morphisms, formulated internally to `C`. We assume that `F` is fully faithful here.

We also provide some basic API for dealing with triple pullbacks, i.e. given
`hf₁ : relativelyRepresentable f₁`, `f₂ : F.obj A₂ ⟶ X` and `f₃ : F.obj A₃ ⟶ X`, we define
`hf₁.pullback₃ f₂ f₃` to be the pullback of `(A₁ ×_X A₂) ×_{A₁} (A₁ ×_X A₃)`. We then develop
some API for working with this object, mirroring the usual API for pullbacks, but where as much
as possible is phrased internally to `C`.

## Main results

* `relativelyRepresentable.isMultiplicative`: The class of relatively representable morphisms is
  multiplicative.
* `relativelyRepresentable.isStableUnderBaseChange`: Being relatively representable is stable under
  base change.
* `relativelyRepresentable.of_isIso`: Isomorphisms are relatively representable.

-/

namespace CategoryTheory

open Category Limits MorphismProperty

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)

def Functor.relativelyRepresentable : MorphismProperty D :=
  fun X Y f ↦ ∀ ⦃a : C⦄ (g : F.obj a ⟶ Y), ∃ (b : C) (snd : b ⟶ a)
    (fst : F.obj b ⟶ X), IsPullback fst (F.map snd) f g

namespace Functor.relativelyRepresentable

variable {F}

variable {X Y : D} {f : X ⟶ Y} (hf : F.relativelyRepresentable f)
  {b : C} {f' : F.obj b ⟶ Y} (hf' : F.relativelyRepresentable f')
  {a : C} (g : F.obj a ⟶ Y) (hg : F.relativelyRepresentable g)

noncomputable def pullback : C :=
  (hf g).choose

noncomputable abbrev snd : hf.pullback g ⟶ a :=
  (hf g).choose_spec.choose

noncomputable abbrev fst : F.obj (hf.pullback g) ⟶ X :=
  (hf g).choose_spec.choose_spec.choose

noncomputable abbrev fst' [Full F] : hf'.pullback g ⟶ b :=
  F.preimage (hf'.fst g)

lemma map_fst' [Full F] : F.map (hf'.fst' g) = hf'.fst g :=
  F.map_preimage _

lemma isPullback : IsPullback (hf.fst g) (F.map (hf.snd g)) f g :=
  (hf g).choose_spec.choose_spec.choose_spec
