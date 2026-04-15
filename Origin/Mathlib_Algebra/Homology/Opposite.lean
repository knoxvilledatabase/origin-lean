/-
Extracted from Algebra/Homology/Opposite.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Opposite categories of complexes
Given a preadditive category `V`, the opposite of its category of chain complexes is equivalent to
the category of cochain complexes of objects in `Vᵒᵖ`. We define this equivalence, and another
analogous equivalence (for a general category of homological complexes with a general
complex shape).

We then show that when `V` is abelian, if `C` is a homological complex, then the homology of
`op(C)` is isomorphic to `op` of the homology of `C` (and the analogous result for `unop`).

## Implementation notes
It is convenient to define both `op` and `opSymm`; this is because given a complex shape `c`,
`c.symm.symm` is not defeq to `c`.

## Tags
opposite, chain complex, cochain complex, homology, cohomology, homological complex
-/

noncomputable section

open Opposite CategoryTheory CategoryTheory.Limits

variable {V : Type*} [Category* V] [Abelian V]

theorem imageToKernel_op {X Y Z : V} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0) :
    imageToKernel g.op f.op (by rw [← op_comp, w, op_zero]) =
      (imageSubobjectIso _ ≪≫ (imageOpOp _).symm).hom ≫
        (cokernel.desc f (factorThruImage g)
              (by rw [← cancel_mono (image.ι g), Category.assoc, image.fac, w, zero_comp])).op ≫
          (kernelSubobjectIso _ ≪≫ kernelOpOp _).inv := by
  ext
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, kernelOpOp_inv, Category.assoc,
    imageToKernel_arrow, kernelSubobject_arrow', kernel.lift_ι, ← op_comp, cokernel.π_desc,
    ← imageSubobject_arrow, ← imageUnopOp_inv_comp_op_factorThruImage g.op]
  rfl

theorem imageToKernel_unop {X Y Z : Vᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0) :
    imageToKernel g.unop f.unop (by rw [← unop_comp, w, unop_zero]) =
      (imageSubobjectIso _ ≪≫ (imageUnopUnop _).symm).hom ≫
        (cokernel.desc f (factorThruImage g)
              (by rw [← cancel_mono (image.ι g), Category.assoc, image.fac, w, zero_comp])).unop ≫
          (kernelSubobjectIso _ ≪≫ kernelUnopUnop _).inv := by
  ext
  dsimp only [imageUnopUnop]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, kernelUnopUnop_inv, Category.assoc,
    imageToKernel_arrow, kernelSubobject_arrow', kernel.lift_ι, cokernel.π_desc, Iso.unop_inv,
    ← unop_comp, factorThruImage_comp_imageUnopOp_inv, Quiver.Hom.unop_op, imageSubobject_arrow]

end

namespace HomologicalComplex

variable {ι V : Type*} [Category* V] {c : ComplexShape ι}

variable [HasZeroMorphisms V]
