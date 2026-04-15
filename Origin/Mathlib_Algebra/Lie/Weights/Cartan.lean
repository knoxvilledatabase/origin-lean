/-
Extracted from Algebra/Lie/Weights/Cartan.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Weights and roots of Lie modules and Lie algebras with respect to Cartan subalgebras

Given a Lie algebra `L` which is not necessarily nilpotent, it may be useful to study its
representations by restricting them to a nilpotent subalgebra (e.g., a Cartan subalgebra). In the
particular case when we view `L` as a module over itself via the adjoint action, the weight spaces
of `L` restricted to a nilpotent subalgebra are known as root spaces.

Basic definitions and properties of the above ideas are provided in this file.

## Main definitions

  * `LieAlgebra.rootSpace`
  * `LieAlgebra.corootSpace`
  * `LieAlgebra.rootSpaceWeightSpaceProduct`
  * `LieAlgebra.rootSpaceProduct`
  * `LieAlgebra.zeroRootSubalgebra_eq_iff_is_cartan`

-/

open Set

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (H : LieSubalgebra R L) [LieRing.IsNilpotent H]
  {M : Type*} [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

namespace LieAlgebra

open scoped TensorProduct

open TensorProduct.LieModule LieModule

abbrev rootSpace (χ : H → R) : LieSubmodule R H L :=
  genWeightSpace L χ

theorem zero_rootSpace_eq_top_of_nilpotent [LieRing.IsNilpotent L] :
    rootSpace (⊤ : LieSubalgebra R L) 0 = ⊤ :=
  zero_genWeightSpace_eq_top_of_nilpotent L
