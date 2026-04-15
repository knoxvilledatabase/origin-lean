/-
Extracted from Algebra/Homology/ImageToKernel.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Image-to-kernel comparison maps

Whenever `f : A ⟶ B` and `g : B ⟶ C` satisfy `w : f ≫ g = 0`,
we have `image_le_kernel f g w : imageSubobject f ≤ kernelSubobject g`
(assuming the appropriate images and kernels exist).

`imageToKernel f g w` is the corresponding morphism between objects in `C`.

-/

universe v u w

open CategoryTheory CategoryTheory.Limits

variable {ι : Type*}

variable {V : Type u} [Category.{v} V] [HasZeroMorphisms V]

noncomputable section

variable {A B C : V} (f : A ⟶ B) [HasImage f] (g : B ⟶ C) [HasKernel g]

theorem image_le_kernel (w : f ≫ g = 0) : imageSubobject f ≤ kernelSubobject g :=
  imageSubobject_le_mk _ _ (kernel.lift _ _ w) (by simp)

def imageToKernel (w : f ≫ g = 0) : (imageSubobject f : V) ⟶ (kernelSubobject g : V) :=
  Subobject.ofLE _ _ (image_le_kernel _ _ w)

-- INSTANCE (free from Core): (w
