/-
Extracted from Algebra/Homology/ShortComplex/Abelian.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Abelian categories have homology

In this file, it is shown that all short complexes `S` in abelian
categories have terms of type `S.HomologyData`.

The strategy of the proof is to study the morphism
`kernel.ι S.g ≫ cokernel.π S.f`. We show that there is a
`LeftHomologyData` for `S` for which the `H` field consists
of the coimage of `kernel.ι S.g ≫ cokernel.π S.f`, while
there is a `RightHomologyData` for which the `H` is the
image of `kernel.ι S.g ≫ cokernel.π S.f`. The fact that
these left and right homology data are compatible (i.e.
provide a `HomologyData`) is obtained by using the
coimage-image isomorphism in abelian categories.

We also provide a constructor `HomologyData.ofEpiMonoFactorisation`
which takes as an input an epi-mono factorization `kf.pt ⟶ H ⟶ cc.pt`
of `kf.ι ≫ cc.π` where `kf` is a limit kernel fork of `S.g` and
`cc` is a limit cokernel cofork of `S.f`.

-/

universe v v' u u'

namespace CategoryTheory

open Category Limits

variable {C : Type u} [Category.{v} C] [Abelian C] (S : ShortComplex C)
  {D : Type u'} [Category.{v'} D] [HasZeroMorphisms D]

namespace ShortComplex

noncomputable def abelianImageToKernel : Abelian.image S.f ⟶ kernel S.g :=
  kernel.lift S.g (Abelian.image.ι S.f)
    (by simp only [← cancel_epi (Abelian.factorThruImage S.f),
      kernel.lift_ι_assoc, zero, comp_zero])
