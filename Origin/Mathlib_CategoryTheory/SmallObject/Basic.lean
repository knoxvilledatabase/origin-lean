/-
Extracted from CategoryTheory/SmallObject/Basic.lean
Genuine: 4 of 8 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# The small object argument

Let `C` be a category. A class of morphisms `I : MorphismProperty C`
permits the small object argument (typeclass `HasSmallObjectArgument.{w} I`
where `w` is an auxiliary universe) if there exists a regular
cardinal `κ : Cardinal.{w}` such that `IsCardinalForSmallObjectArgument I κ`
holds. This technical condition is defined in the file
`Mathlib/CategoryTheory/SmallObject/IsCardinalForSmallObjectArgument.lean`. It involves certain
smallness conditions relative to `w`, the existence of certain colimits in `C`,
and for each object `A` which is the source of a morphism in `I`,
the `Hom(A, -)` functor (`coyoneda.obj (op A)`) should commute
to transfinite compositions of pushouts of coproducts of morphisms in `I`
(this condition is automatically satisfied for a suitable `κ` when `A` is a
presentable object of `C`, see the file `Mathlib/CategoryTheory/Presentable/Basic.lean`).

## Main results

Assuming `I` permits the small object argument, the two main results
obtained in this file are:
* the class `I.rlp.llp` of morphisms that have the left lifting property with
  respect to the maps that have the right lifting property with respect
  to `I` are exactly the retracts of transfinite compositions (indexed
  by a suitable well-ordered type `J`) of pushouts of coproducts of
  morphisms in `I`;
* morphisms in `C` have a functorial factorization as a morphism in
  `I.rlp.llp` followed by a morphism in `I.rlp`.

In the context of model categories, these results are known as Quillen's small object
argument (originally for `J := ℕ`). Actually, the more general construction by
transfinite induction already appeared in the proof of the existence of enough
injectives in abelian categories with AB5 and a generator by Grothendieck, who then
wrote that the "proof was essentially known". Indeed, the argument appeared
in *Homological algebra* by Cartan and Eilenberg (p. 9-10) in the case of modules,
and they mention that the result was initially obtained by Baer.

## Structure of the proof

The main part in the proof is the construction of the functorial factorization.
This involves a construction by transfinite induction. A general
procedure for constructions by transfinite
induction in categories (including the iteration of a functor)
is done in the file `Mathlib/CategoryTheory/SmallObject/TransfiniteIteration.lean`.
The factorization of the small object argument is obtained by doing
a transfinite iteration of a specific functor `Arrow C ⥤ Arrow C` which
is defined in the file `Mathlib/CategoryTheory/SmallObject/Construction.lean` (this definition
involves coproducts and a pushout). These ingredients are combined
in the file `Mathlib/CategoryTheory/SmallObject/IsCardinalForSmallObjectArgument.lean`
where the main results are obtained under a `IsCardinalForSmallObjectArgument I κ`
assumption. The fact that the left lifting property with respect to
a class of morphisms is stable by transfinite compositions was obtained in
the file `Mathlib/CategoryTheory/SmallObject/TransfiniteCompositionLifting.lean`.

## References

- [Henri Cartan and Samuel Eilenberg, *Homological algebra*][cartan-eilenberg-1956]
- [Alexander Grothendieck, *Sur quelques points d'algèbre homologique*][grothendieck-1957]
- [Daniel G. Quillen, *Homotopical algebra*][Quillen1967]
- https://ncatlab.org/nlab/show/small+object+argument

-/

universe w v u

namespace CategoryTheory

open Category Limits SmallObject

namespace MorphismProperty

variable {C : Type u} [Category.{v} C] (I : MorphismProperty C)

class HasSmallObjectArgument : Prop where
  exists_cardinal : ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular) (_ : OrderBot κ.ord.ToType),
    IsCardinalForSmallObjectArgument I κ

variable [HasSmallObjectArgument.{w} I]

noncomputable def smallObjectκ : Cardinal.{w} :=
  (HasSmallObjectArgument.exists_cardinal (I := I)).choose

-- INSTANCE (free from Core): smallObjectκ_isRegular

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): isCardinalForSmallObjectArgument_smallObjectκ

-- INSTANCE (free from Core): :

lemma llp_rlp_of_hasSmallObjectArgument' :
    I.rlp.llp = (transfiniteCompositionsOfShape (coproducts.{w} I).pushouts
        I.smallObjectκ.ord.ToType).retracts :=
  llp_rlp_of_isCardinalForSmallObjectArgument' I I.smallObjectκ

lemma llp_rlp_of_hasSmallObjectArgument :
    I.rlp.llp =
      (transfiniteCompositions.{w} (coproducts.{w} I).pushouts).retracts :=
  llp_rlp_of_isCardinalForSmallObjectArgument I I.smallObjectκ

end MorphismProperty

end CategoryTheory
