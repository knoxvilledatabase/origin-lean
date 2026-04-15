/-
Extracted from FieldTheory/Galois/GaloisClosure.lean
Genuine: 2 of 17 | Dissolved: 0 | Infrastructure: 15
-/
import Origin.Core

/-!

# Main definitions and results

In a field extension `K/k`

* `FiniteGaloisIntermediateField` : The type of intermediate fields of `K/k`
  that are finite and Galois over `k`

* `adjoin` : The finite Galois intermediate field obtained from the normal closure of adjoining a
  finite `s : Set K` to `k`.

## TODO

* `FiniteGaloisIntermediateField` should be a `ConditionallyCompleteLattice` but isn't proved yet.

-/

open IntermediateField

variable (k K : Type*) [Field k] [Field K] [Algebra k K]

structure FiniteGaloisIntermediateField extends IntermediateField k K where
  [finiteDimensional : FiniteDimensional k toIntermediateField]
  [isGalois : IsGalois k toIntermediateField]

namespace FiniteGaloisIntermediateField

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): (L

-- INSTANCE (free from Core): (L

variable {k K}

lemma val_injective : Function.Injective (toIntermediateField (k := k) (K := K)) := by
  rintro ⟨⟩ ⟨⟩ eq
  simpa only [mk.injEq] using eq

-- INSTANCE (free from Core): (L₁

-- INSTANCE (free from Core): (L₁

-- INSTANCE (free from Core): (L₁

-- INSTANCE (free from Core): (L₁

-- INSTANCE (free from Core): (L₁

-- INSTANCE (free from Core): (L₁

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :
