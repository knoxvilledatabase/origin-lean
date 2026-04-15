/-
Extracted from FieldTheory/IntermediateField/ExtendRight.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Extending intermediate fields to a larger extension

Given a tower of field extensions `K ⊆ L ⊆ M` and an intermediate field `F` of `L/K`, this file
defines `IntermediateField.extendRight F M`, the image of `F` under the inclusion `L ⊆ M`,
as an intermediate field of `M/K`. It is canonically isomorphic to `F` as a `K`-algebra.

The main motivation is to embed a subextension `F/K` of `L/K` into a larger extension `M/K`.
This is useful for instance when one needs `M/K` to be Galois.

## Main definitions

- `IntermediateField.extendRight F M`: the intermediate field of `M/K` defined as the image of `F`
  under the map `L →ₐ[K] M`.
- `IntermediateField.extendRightEquiv F M`: the `K`-algebra isomorphism `F ≃ₐ[K] extendRight F M`.

## Main instances

- `IntermediateField.extendRight.algebra`: for `S` with `Algebra S F`, `S` acts
  on `extendRight F M`.
- `IntermediateField.extendRight.isFractionRing`: transfers the `IsFractionRing S F` instance.
- `IntermediateField.extendRight.isIntegralClosure`: transfers the
  `IsIntegralClosure S R F` instance.
-/

namespace IntermediateField

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (F : IntermediateField K L)
  (M : Type*) [Field M] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

def extendRight : IntermediateField K M := F.map (Algebra.algHom K L M)

noncomputable def extendRightEquiv : F ≃ₐ[K] (F.extendRight M) := F.equivMap (Algebra.algHom K L M)
