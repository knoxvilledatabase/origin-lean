/-
Extracted from CategoryTheory/Limits/Shapes/Reflexive.lean
Genuine: 7 of 7 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Reflexive coequalizers

This file deals with reflexive pairs, which are pairs of morphisms with a common section.

A reflexive coequalizer is a coequalizer of such a pair. These kind of coequalizers often enjoy
nicer properties than general coequalizers, and feature heavily in some versions of the monadicity
theorem.

We also give some examples of reflexive pairs: for an adjunction `F ⊣ G` with counit `ε`, the pair
`(FGε_B, ε_FGB)` is reflexive. If a pair `f,g` is a kernel pair for some morphism, then it is
reflexive.

## Main definitions

* `IsReflexivePair` is the predicate that f and g have a common section.
* `WalkingReflexivePair` is the diagram indexing pairs with a common section.
* A `reflexiveCofork` is a cocone on a diagram indexed by `WalkingReflexivePair`.
* `WalkingReflexivePair.inclusionWalkingReflexivePair` is the inclusion functor from
  `WalkingParallelPair` to `WalkingReflexivePair`. It acts on reflexive pairs as forgetting
  the common section.
* `HasReflexiveCoequalizers` is the predicate that a category has all colimits of reflexive pairs.
* `reflexiveCoequalizerIsoCoequalizer`: an isomorphism promoting the coequalizer of a reflexive pair
  to the colimit of a diagram out of the walking reflexive pair.

## Main statements

* `IsKernelPair.isReflexivePair`: A kernel pair is a reflexive pair
* `WalkingParallelPair.inclusionWalkingReflexivePair_final`: The inclusion functor is final.
* `hasReflexiveCoequalizers_iff`: A category has coequalizers of reflexive pairs if and only if it
  has all colimits of shape `WalkingReflexivePair`.

## TODO
* If `C` has binary coproducts and reflexive coequalizers, then it has all coequalizers.
* If `T` is a monad on cocomplete category `C`, then `Algebra T` is cocomplete iff it has reflexive
  coequalizers.
* If `C` is locally Cartesian closed and has reflexive coequalizers, then it has images: in fact
  regular epi (and hence strong epi) images.
* Bundle the reflexive pairs of kernel pairs and of adjunction as functors out of the walking
  reflexive pair.
-/

namespace CategoryTheory

universe v v₂ u u₂

variable {C : Type u} [Category.{v} C]

variable {D : Type u₂} [Category.{v₂} D]

variable {A B : C} {f g : A ⟶ B}

class IsReflexivePair (f g : A ⟶ B) : Prop where
  common_section' : ∃ s : B ⟶ A, s ≫ f = 𝟙 B ∧ s ≫ g = 𝟙 B

theorem IsReflexivePair.common_section (f g : A ⟶ B) [IsReflexivePair f g] :
    ∃ s : B ⟶ A, s ≫ f = 𝟙 B ∧ s ≫ g = 𝟙 B := IsReflexivePair.common_section'

class IsCoreflexivePair (f g : A ⟶ B) : Prop where
  common_retraction' : ∃ s : B ⟶ A, f ≫ s = 𝟙 A ∧ g ≫ s = 𝟙 A

theorem IsCoreflexivePair.common_retraction (f g : A ⟶ B) [IsCoreflexivePair f g] :
    ∃ s : B ⟶ A, f ≫ s = 𝟙 A ∧ g ≫ s = 𝟙 A := IsCoreflexivePair.common_retraction'

theorem IsReflexivePair.mk' (s : B ⟶ A) (sf : s ≫ f = 𝟙 B) (sg : s ≫ g = 𝟙 B) :
    IsReflexivePair f g :=
  ⟨⟨s, sf, sg⟩⟩

theorem IsCoreflexivePair.mk' (s : B ⟶ A) (fs : f ≫ s = 𝟙 A) (gs : g ≫ s = 𝟙 A) :
    IsCoreflexivePair f g :=
  ⟨⟨s, fs, gs⟩⟩

noncomputable def commonSection (f g : A ⟶ B) [IsReflexivePair f g] : B ⟶ A :=
  (IsReflexivePair.common_section f g).choose
