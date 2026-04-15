/-
Extracted from CategoryTheory/Abelian/Subcategory.lean
Genuine: 2 of 5 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Subcategories of abelian categories

Let `C` be an abelian category. Given `P : ObjectProperty C` which contains
zero, is closed under kernels, cokernels and finite products, we show that the
full subcategory defined by `P` is abelian.

-/

namespace CategoryTheory.ObjectProperty

open Limits

variable {C : Type*} [Category* C] (P : ObjectProperty C)

lemma preservesMonomorphisms_ι_of_isNormalEpiCategory [HasZeroMorphisms C] [HasFiniteCoproducts C]
    [HasKernels C] [HasCokernels C] [IsNormalEpiCategory C] [HasZeroObject C] [P.ContainsZero]
    [P.IsClosedUnderKernels] : P.ι.PreservesMonomorphisms :=
  have := P.preservesKernels_ι
  NormalEpiCategory.preservesMonomorphisms_of_preservesKernels P.ι

-- INSTANCE (free from Core): [Abelian

lemma preservesEpimorphisms_ι_of_isNormalMonoCategory [HasZeroMorphisms C] [HasFiniteProducts C]
    [HasKernels C] [HasCokernels C] [IsNormalMonoCategory C] [HasZeroObject C] [P.ContainsZero]
    [P.IsClosedUnderCokernels] : P.ι.PreservesEpimorphisms :=
  have := P.preservesCokernels_ι
  NormalMonoCategory.preservesEpimorphisms_of_preservesCokernels P.ι

-- INSTANCE (free from Core): [Abelian

-- INSTANCE (free from Core): [Abelian

end CategoryTheory.ObjectProperty
