/-
Extracted from AlgebraicTopology/Quasicategory/StrictBicategory.lean
Genuine: 2 of 5 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# The strict bicategory of quasicategories

In this file we define a strict bicategory `QCat.strictBicategory` whose objects
are quasicategories.

This strict category is defined from `QCat.catEnrichedOrdinaryCategory` which is
the `Cat`-enriched ordinary category of quasicategories whose hom-categories are the
homotopy categories of the simplicial internal homs, defined by
applying `hoFunctor : SSet ⥤ Cat`.

As an enriched ordinary category, there is an equivalence `QCat.forgetEnrichment.equiv`
between the underlying category and the full subcategory of quasicategories. Thus the
`1`-morphisms of `QCat.strictBicategory` are maps of simplicial sets.

Future work will use the fact that quasicategories define a cartesian closed subcategory
of simplicial sets to identify the `2`-morphisms of `QCat.strictBicategory` with
homotopy classes of homotopies between them, defined using the simplicial interval `Δ[1]`.

This strict bicategory serves as a setting to develop the formal category theory of quasicategories.

## References

* [Emily Riehl and Dominic Verity, Elements of ∞-Category Theory][RiehlVerity2022]
* [Emily Riehl and Dominic Verity, The 2-category theory of quasi-categories][RiehlVerity2015]

-/

universe u

namespace SSet

open CategoryTheory Simplicial

abbrev QCat := ObjectProperty.FullSubcategory Quasicategory

-- INSTANCE (free from Core): QCat.catEnrichedOrdinaryCategory

def QCat.forgetEnrichment.equiv :
    ForgetEnrichment Cat QCat ≌ QCat := ForgetEnrichment.equiv Cat

-- INSTANCE (free from Core): QCat.bicategory

-- INSTANCE (free from Core): QCat.strictBicategory

end SSet
