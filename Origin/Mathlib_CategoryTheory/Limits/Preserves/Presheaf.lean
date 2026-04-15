/-
Extracted from CategoryTheory/Limits/Preserves/Presheaf.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Finite-limit-preserving presheaves

In this file we prove that if `C` is a small finitely cocomplete category and `A : Cᵒᵖ ⥤ Type u`
is a presheaf, then `CostructuredArrow yoneda A` is filtered (equivalently, the category of
elements of `A` is cofiltered) if and only if `A` preserves finite limits.

This is one of the keys steps of establishing the equivalence `Ind C ≌ (Cᵒᵖ ⥤ₗ Type u)` (here,
`Cᵒᵖ ⥤ₗ Type u` is the category of left exact functors) for a *small* finitely cocomplete category
`C`.

## Implementation notes

In the entire file, we are careful about details like functor associativity to ensure that we do
not end up in situations where we have morphisms like `colimit.ι F i ≫ f`, where the domain of `f`
is `colimit G` where `F` and `G` are definitionally equal but not syntactically equal. In these
situations, lemmas about `colimit.ι G i ≫ f` cannot be applied using `rw` and `simp`, forcing the
use of `erw`. In particular, for us this means that `HasColimit.isoOfNatIso (Iso.refl _)` is better
than `Iso.refl _` and that we should be very particular about functor associativity.

The theorem is also true for large categories and the proof given here generalizes to this case on
paper. However, our infrastructure for commuting finite limits of shape `J` and filtered colimits
of shape `K` is fundamentally not equipped to deal with the case where not all limits of shape `K`
exist. In fact, not even the definition `colimitLimitToLimitColimit` can be written down if not
all limits of shape `K` exist. Refactoring this to the level of generality we need would be a major
undertaking. Since the application to the category of Ind-objects only require the case where `C`
is small, we leave this as a TODO.

## References
* [M. Kashiwara, P. Schapira, *Categories and Sheaves*][Kashiwara2006], Proposition 3.3.13
* [F. Borceux, *Handbook of Categorical Algebra 1*][borceux-vol1], Proposition 6.1.2
-/

open CategoryTheory Limits Functor

universe v u

namespace CategoryTheory.Limits

section LargeCategory

variable {C : Type u} [Category.{v} C] [HasFiniteColimits C] (A : Cᵒᵖ ⥤ Type v)

theorem isFiltered_costructuredArrow_yoneda_of_preservesFiniteLimits
    [PreservesFiniteLimits A] : IsFiltered (CostructuredArrow yoneda A) := by
  suffices IsCofiltered A.Elements from
    IsFiltered.of_equivalence (CategoryOfElements.costructuredArrowYonedaEquivalence _)
  suffices HasFiniteLimits A.Elements from IsCofiltered.of_hasFiniteLimits A.Elements
  exact ⟨fun J _ _ => inferInstance⟩

end LargeCategory

variable {C : Type u} [SmallCategory C] [HasFiniteColimits C]

variable (A : Cᵒᵖ ⥤ Type u)

namespace PreservesFiniteLimitsOfIsFilteredCostructuredArrowYonedaAux

variable {J : Type} [SmallCategory J] [FinCategory J] (K : J ⥤ Cᵒᵖ)

def functorToInterchange : J ⥤ CostructuredArrow yoneda A ⥤ Type u :=
  K ⋙ coyoneda ⋙ (whiskeringLeft _ _ _).obj (CostructuredArrow.proj _ _)
