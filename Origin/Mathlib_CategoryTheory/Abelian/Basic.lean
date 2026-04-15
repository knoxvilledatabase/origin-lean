/-
Extracted from CategoryTheory/Abelian/Basic.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Abelian categories

This file contains the definition and basic properties of abelian categories.

There are many definitions of abelian category. Our definition is as follows:
A category is called abelian if it is preadditive,
has finite products, kernels, and cokernels,
and if every monomorphism and epimorphism is normal.

It should be noted that if we also assume finite coproducts, then preadditivity is
actually a consequence of the other properties, as we show in
`Mathlib/CategoryTheory/Abelian/NonPreadditive.lean`. However, this fact is of little practical
relevance, since essentially all interesting abelian categories come with a
preadditive structure. In this way, by requiring preadditivity, we allow the
user to pass in the "native" preadditive structure for the specific category they are
working with.

## Main definitions

* `Abelian` is the type class indicating that a category is abelian. It extends `Preadditive`.
* `Abelian.image f` is `kernel (cokernel.π f)`, and
* `Abelian.coimage f` is `cokernel (kernel.ι f)`.

## Main results

* In an abelian category, mono + epi = iso.
* If `f : X ⟶ Y`, then the map `factorThruImage f : X ⟶ image f` is an epimorphism, and the map
  `factorThruCoimage f : coimage f ⟶ Y` is a monomorphism.
* Factoring through the image and coimage is a strong epi-mono factorisation. This means that
  * every abelian category has images. We provide the isomorphism
    `imageIsoImage : abelian.image f ≅ limits.image f`.
  * the canonical morphism `coimageImageComparison : coimage f ⟶ image f`
    is an isomorphism.
* We provide the alternate characterisation of an abelian category as a category with
  (co)kernels and finite products, and in which the canonical coimage-image comparison morphism
  is always an isomorphism.
* Every epimorphism is a cokernel of its kernel. Every monomorphism is a kernel of its cokernel.
* The pullback of an epimorphism is an epimorphism. The pushout of a monomorphism is a monomorphism.
  (This is not to be confused with the fact that the pullback of a monomorphism is a monomorphism,
  which is true in any category).

## Implementation notes

The typeclass `Abelian` does not extend `NonPreadditiveAbelian`,
to avoid having to deal with comparing the two `HasZeroMorphisms` instances
(one from `Preadditive` in `Abelian`, and the other a field of `NonPreadditiveAbelian`).
As a consequence, at the beginning of this file we trivially build
a `NonPreadditiveAbelian` instance from an `Abelian` instance,
and use this to restate a number of theorems,
in each case just reusing the proof from `Mathlib/CategoryTheory/Abelian/NonPreadditive.lean`.

We don't show this yet, but abelian categories are finitely complete and finitely cocomplete.
However, the limits we can construct at this level of generality will most likely be less nice than
the ones that can be created in specific applications. For this reason, we adopt the following
convention:

* If the statement of a theorem involves limits, the existence of these limits should be made an
  explicit typeclass parameter.
* If a limit only appears in a proof, but not in the statement of a theorem, the limit should not
  be a typeclass parameter, but instead be created using `Abelian.hasPullbacks` or a similar
  definition.

## References

* [F. Borceux, *Handbook of Categorical Algebra 2*][borceux-vol2]
* [P. Aluffi, *Algebra: Chapter 0*][aluffi2016]

-/

noncomputable section

open CategoryTheory

open CategoryTheory.Preadditive

open CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

variable (C)

class Abelian extends Preadditive C, IsNormalMonoCategory C, IsNormalEpiCategory C where
  [has_finite_products : HasFiniteProducts C]
  [has_kernels : HasKernels C]
  [has_cokernels : HasCokernels C]

-- INSTANCE (free from Core): 100]

-- INSTANCE (free from Core): 100]

end CategoryTheory

open CategoryTheory

/-!
We begin by providing an alternative constructor:
a preadditive category with kernels, cokernels, and finite products,
in which the coimage-image comparison morphism is always an isomorphism,
is an abelian category.
-/

namespace CategoryTheory.Abelian

variable {C : Type u} [Category.{v} C] [Preadditive C]

variable [Limits.HasKernels C] [Limits.HasCokernels C]

namespace OfCoimageImageComparisonIsIso
