/-
Extracted from CategoryTheory/Abelian/Images.lean
Genuine: 8 of 10 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# The abelian image and coimage.

In an abelian category we usually want the image of a morphism `f` to be defined as
`kernel (cokernel.π f)`, and the coimage to be defined as `cokernel (kernel.ι f)`.

We make these definitions here, as `Abelian.image f` and `Abelian.coimage f`
(without assuming the category is actually abelian),
and later relate these to the usual categorical notions when in an abelian category.

There is a canonical morphism `coimageImageComparison : Abelian.coimage f ⟶ Abelian.image f`.
Later we show that this is always an isomorphism in an abelian category,
and conversely a category with (co)kernels and finite products in which this morphism
is always an isomorphism is an abelian category.
-/

noncomputable section

universe v u

open CategoryTheory

open CategoryTheory.Limits

namespace CategoryTheory.Abelian

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

variable {P Q : C} (f : P ⟶ Q)

section Image

variable [HasCokernel f] [HasKernel (cokernel.π f)]

protected abbrev image : C :=
  kernel (cokernel.π f)

protected abbrev image.ι : Abelian.image f ⟶ Q :=
  kernel.ι (cokernel.π f)

protected abbrev factorThruImage : P ⟶ Abelian.image f :=
  kernel.lift (cokernel.π f) f <| cokernel.condition f

protected theorem image.fac : Abelian.factorThruImage f ≫ image.ι f = f :=
  kernel.lift_ι _ _ _

-- INSTANCE (free from Core): mono_factorThruImage

end Image

section Coimage

variable [HasKernel f] [HasCokernel (kernel.ι f)]

protected abbrev coimage : C :=
  cokernel (kernel.ι f)

protected abbrev coimage.π : P ⟶ Abelian.coimage f :=
  cokernel.π (kernel.ι f)

protected abbrev factorThruCoimage : Abelian.coimage f ⟶ Q :=
  cokernel.desc (kernel.ι f) f <| kernel.condition f

protected theorem coimage.fac : coimage.π f ≫ Abelian.factorThruCoimage f = f :=
  cokernel.π_desc _ _ _

-- INSTANCE (free from Core): epi_factorThruCoimage

end Coimage

section Comparison

variable [HasCokernel f] [HasKernel f] [HasKernel (cokernel.π f)] [HasCokernel (kernel.ι f)]
