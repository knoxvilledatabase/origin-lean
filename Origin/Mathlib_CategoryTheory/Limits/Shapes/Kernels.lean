/-
Extracted from CategoryTheory/Limits/Shapes/Kernels.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Kernels and cokernels

In a category with zero morphisms, the kernel of a morphism `f : X ⟶ Y` is
the equalizer of `f` and `0 : X ⟶ Y`. (Similarly the cokernel is the coequalizer.)

The basic definitions are
* `kernel : (X ⟶ Y) → C`

* `kernel.ι : kernel f ⟶ X`
* `kernel.condition : kernel.ι f ≫ f = 0` and
* `kernel.lift (k : W ⟶ X) (h : k ≫ f = 0) : W ⟶ kernel f` (as well as the dual versions)

## Main statements

Besides the definition and lifts, we prove
* `kernel.ιZeroIsIso`: a kernel map of a zero morphism is an isomorphism
* `kernel.eq_zero_of_epi_kernel`: if `kernel.ι f` is an epimorphism, then `f = 0`
* `kernel.ofMono`: the kernel of a monomorphism is the zero object
* `kernel.liftMono`: the lift of a monomorphism `k : W ⟶ X` such that `k ≫ f = 0`
  is still a monomorphism
* `kernel.isLimitConeZeroCone`: if our category has a zero object, then the map from the zero
  object is a kernel map of any monomorphism
* `kernel.ιOfZero`: `kernel.ι (0 : X ⟶ Y)` is an isomorphism

and the corresponding dual statements.

## Future work
* TODO: connect this with existing work in the group theory and ring theory libraries.

## Implementation notes
As with the other special shapes in the limits library, all the definitions here are given as
`abbrev`s of the general statements for limits, so all the `simp` lemmas and theorems about
general limits can be used.

## References

* [F. Borceux, *Handbook of Categorical Algebra 2*][borceux-vol2]
-/

noncomputable section

universe v v₂ u u' u₂

open CategoryTheory

open CategoryTheory.Limits.WalkingParallelPair

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

variable [HasZeroMorphisms C]

abbrev HasKernel {X Y : C} (f : X ⟶ Y) : Prop :=
  HasLimit (parallelPair f 0)

abbrev HasCokernel {X Y : C} (f : X ⟶ Y) : Prop :=
  HasColimit (parallelPair f 0)

variable {X Y : C} (f : X ⟶ Y)

abbrev KernelFork :=
  Fork f 0

variable {f}
