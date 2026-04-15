/-
Extracted from Algebra/AffineMonoid/Embedding.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Affine monoids embed into `ℤⁿ`

This file proves that finitely generated cancellative torsion-free commutative monoids embed into
`ℤⁿ` for some `n`.
-/

open Algebra AddLocalization Function

variable {M : Type*} [AddCancelCommMonoid M] [AddMonoid.FG M] [IsAddTorsionFree M]

namespace AffineAddMonoid

variable (M) in

noncomputable abbrev dim := Module.finrank ℤ <| GrothendieckAddGroup M

variable (M) in

noncomputable def embedding : M →+ FreeAbelianGroup (Fin (dim M)) :=
  .comp (FreeAbelianGroup.equivFinsupp _).symm.toAddMonoidHom <|
    .comp (Module.finBasis ℤ _).repr.toAddMonoidHom
      (addMonoidOf ⊤).toAddMonoidHom

lemma embedding_injective : Injective (embedding M) := by
  simpa [embedding] using mk_left_injective 0

end AffineAddMonoid
