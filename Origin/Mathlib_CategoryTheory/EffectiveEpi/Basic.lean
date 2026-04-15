/-
Extracted from CategoryTheory/EffectiveEpi/Basic.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Effective epimorphisms

We define the notion of effective epimorphism and effective epimorphic family of morphisms.

A morphism is an *effective epi* if it is a joint coequalizer of all pairs of
morphisms which it coequalizes.

A family of morphisms with fixed target is *effective epimorphic* if it is initial among families
of morphisms with its sources and a general fixed target, coequalizing every pair of morphisms it
coequalizes (here, the pair of morphisms coequalized can have different targets among the sources
of the family).

We have defined the notion of effective epi for morphisms and families of morphisms in such a
way that avoids requiring the existence of pullbacks. However, if the relevant pullbacks exist
then these definitions are equivalent, see the file
`Mathlib/CategoryTheory/EffectiveEpi/RegularEpi.lean`
See [nlab: *Effective Epimorphism*](https://ncatlab.org/nlab/show/effective+epimorphism) and
[Stacks 00WP](https://stacks.math.columbia.edu/tag/00WP) for the standard definitions. Note that
our notion of `EffectiveEpi` is often called "strict epi" in the literature.

## References
- [Elephant]: *Sketches of an Elephant*, P. T. Johnstone: C2.1, Example 2.1.12.
- [nlab: *Effective Epimorphism*](https://ncatlab.org/nlab/show/effective+epimorphism) and
- [Stacks 00WP](https://stacks.math.columbia.edu/tag/00WP) for the standard definitions.

-/

namespace CategoryTheory

open Limits Category

variable {C : Type*} [Category* C]

structure EffectiveEpiStruct {X Y : C} (f : Y ⟶ X) where
  /--
  For every `W` with a morphism `e : Y ⟶ W` that coequalizes every pair of morphisms
  `g₁ g₂ : Z ⟶ Y` which `f` coequalizes, `desc e h` is a morphism `X ⟶ W`...
  -/
  desc : ∀ {W : C} (e : Y ⟶ W),
    (∀ {Z : C} (g₁ g₂ : Z ⟶ Y), g₁ ≫ f = g₂ ≫ f → g₁ ≫ e = g₂ ≫ e) → (X ⟶ W)
  /-- ...factorizing `e` through `f`... -/
  fac : ∀ {W : C} (e : Y ⟶ W)
    (h : ∀ {Z : C} (g₁ g₂ : Z ⟶ Y), g₁ ≫ f = g₂ ≫ f → g₁ ≫ e = g₂ ≫ e),
    f ≫ desc e h = e
  /-- ...and as such, unique. -/
  uniq : ∀ {W : C} (e : Y ⟶ W)
    (h : ∀ {Z : C} (g₁ g₂ : Z ⟶ Y), g₁ ≫ f = g₂ ≫ f → g₁ ≫ e = g₂ ≫ e)
    (m : X ⟶ W), f ≫ m = e → m = desc e h

class EffectiveEpi {X Y : C} (f : Y ⟶ X) : Prop where
  /-- `f` is an effective epimorphism if there exists an `EffectiveEpiStruct` for `f`. -/
  effectiveEpi : Nonempty (EffectiveEpiStruct f)

noncomputable

def EffectiveEpi.getStruct {X Y : C} (f : Y ⟶ X) [EffectiveEpi f] : EffectiveEpiStruct f :=
  EffectiveEpi.effectiveEpi.some

noncomputable

def EffectiveEpi.desc {X Y W : C} (f : Y ⟶ X) [EffectiveEpi f]
    (e : Y ⟶ W) (h : ∀ {Z : C} (g₁ g₂ : Z ⟶ Y), g₁ ≫ f = g₂ ≫ f → g₁ ≫ e = g₂ ≫ e) :
    X ⟶ W := (EffectiveEpi.getStruct f).desc e h
