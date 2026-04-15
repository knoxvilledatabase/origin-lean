/-
Extracted from CategoryTheory/Abelian/FreydMitchell.lean
Genuine: 5 of 11 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core

/-!
# The Freyd-Mitchell embedding theorem

Let `C` be an abelian category. We construct a ring `FreydMitchell.EmbeddingRing C` and a functor
`FreydMitchell.embedding : C ⥤ ModuleCat.{max u v} (EmbeddingRing C)` which is full, faithful and
exact.

## Overview of the proof

The usual strategy to prove the Freyd-Mitchell embedding theorem is as follows:

1. Prove that if `D` is a Grothendieck abelian category and `F : C ⥤ Dᵒᵖ` is a functor from a
   small category, then there is a functor `G : Dᵒᵖ ⥤ ModuleCat R` for a suitable `R` such that `G`
   is faithful and exact and `F ⋙ G` is full.
2. Find a suitable Grothendieck abelian category `D` and a full, faithful and exact functor
   `F : C ⥤ Dᵒᵖ`.

To prove (1), we proceed as follows:

1. Using the Special Adjoint Functor Theorem and the duality between subobjects and quotients in
   abelian categories, we have that Grothendieck abelian categories have all limits (this is shown
   in `Mathlib/CategoryTheory/Abelian/GrothendieckCategory/Basic.lean`).
2. Using the small object argument, it is shown that Grothendieck abelian categories have enough
   injectives (see `Mathlib/CategoryTheory/Abelian/GrothendieckCategory/EnoughInjectives.lean`).
3. Putting these two together, it follows that Grothendieck abelian categories have an injective
   cogenerator (see `Mathlib/CategoryTheory/Generator/Abelian.lean`).
4. By taking a coproduct of copies of the injective cogenerator, we find a projective separator `G`
   in `Dᵒᵖ` such that every object in the image of `F` is a quotient of `G`. Then the additive Hom
   functor `Hom(G, ·) : Dᵒᵖ ⥤ ModuleCat (End G)ᵐᵒᵖ` is faithful (because `G` is a separator), left
   exact (because it is a hom functor), right exact (because `G` is projective) and full (because of
   a combination of the aforementioned properties, see
   `Mathlib/CategoryTheory/Abelian/Yoneda.lean`).
   We put this all together in the file
   `Mathlib/CategoryTheory/Abelian/GrothendieckCategory/ModuleEmbedding/Opposite.lean`.

To prove (2), there are multiple options.

* Some sources (for example Freyd's "Abelian Categories") choose `D := LeftExactFunctor C Ab`. The
  main difficulty with this approach is that it is not obvious that `D` is abelian. This approach
  has a very algebraic flavor and requires a relatively large amount of ad-hoc reasoning.
* In the Stacks project, it is suggested to choose `D := Sheaf J Ab` for a suitable Grothendieck
  topology on `Cᵒᵖ` and there are reasons to believe that this `D` is in fact equivalent to
  `LeftExactFunctor C Ab`. This approach translates many of the interesting properties along the
  sheafification adjunction from a category of `Ab`-valued presheaves, which in turn inherits many
  interesting properties from the category of abelian groups.
* Kashiwara and Schapira choose `D := Ind Cᵒᵖ`, which can be shown to be equivalent to
  `LeftExactFunctor C Ab` (see the file `Mathlib/CategoryTheory/Preadditive/Indization.lean`).
  This approach deduces most interesting properties from the category of types.

When work on this theorem commenced in early 2022, all three approaches were quite out of reach.
By the time the theorem was proved in early 2025, both the `Sheaf` approach and the `Ind` approach
were available in mathlib. The code below uses `D := Ind Cᵒᵖ`.

## Implementation notes

In the literature you will generally only find this theorem stated for small categories `C`. In
Lean, we can work around this limitation by passing from `C` to `AsSmall.{max u v} C`, thereby
enlarging the category of modules that we land in (which should be inconsequential in most
applications) so that our embedding theorem applies to all abelian categories. If `C` was already a
small category, then this does not change anything.

## References

* https://stacks.math.columbia.edu/tag/05PL
* [M. Kashiwara, P. Schapira, *Categories and Sheaves*][Kashiwara2006], Section 9.6
-/

universe v u

open CategoryTheory Limits

namespace CategoryTheory.Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace FreydMitchell

open ZeroObject in

-- INSTANCE (free from Core): :

variable (C) in

def EmbeddingRing : Type (max u v) :=
  IsGrothendieckAbelian.OppositeModuleEmbedding.EmbeddingRing
    (Ind.yoneda (C := (AsSmall.{max u v} C)ᵒᵖ)).rightOp

-- INSTANCE (free from Core): :

set_option backward.privateInPublic true in

variable (C) in

private def F : C ⥤ AsSmall.{max u v} C :=
  AsSmall.equiv.functor

set_option backward.privateInPublic true in

variable (C) in

private noncomputable def G : AsSmall.{max u v} C ⥤ (Ind (AsSmall.{max u v} C)ᵒᵖ)ᵒᵖ :=
  Ind.yoneda.rightOp

set_option backward.privateInPublic true in

variable (C) in

private noncomputable def H :
    (Ind (AsSmall.{max u v} C)ᵒᵖ)ᵒᵖ ⥤ ModuleCat.{max u v} (EmbeddingRing C) :=
  IsGrothendieckAbelian.OppositeModuleEmbedding.embedding (G C)

set_option backward.privateInPublic true in

set_option backward.privateInPublic.warn false in

variable (C) in

noncomputable def functor : C ⥤ ModuleCat.{max u v} (EmbeddingRing C) :=
  F C ⋙ G C ⋙ H C

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

end FreydMitchell
