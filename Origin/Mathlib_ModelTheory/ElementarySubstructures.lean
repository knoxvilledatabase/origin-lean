/-
Extracted from ModelTheory/ElementarySubstructures.lean
Genuine: 2 of 6 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Elementary Substructures

## Main Definitions

- A `FirstOrder.Language.ElementarySubstructure` is a substructure where the realization of each
  formula agrees with the realization in the larger model.

## Main Results

- The Tarski-Vaught Test for substructures:
  `FirstOrder.Language.Substructure.isElementary_of_exists` gives a simple criterion for a
  substructure to be elementary.
-/

open FirstOrder

namespace FirstOrder

namespace Language

open Structure

variable {L : Language} {M : Type*} [L.Structure M]

def Substructure.IsElementary (S : L.Substructure M) : Prop :=
  ∀ ⦃n⦄ (φ : L.Formula (Fin n)) (x : Fin n → S), φ.Realize (((↑) : _ → M) ∘ x) ↔ φ.Realize x

variable (L M)

structure ElementarySubstructure where
  /-- The underlying substructure -/
  toSubstructure : L.Substructure M
  isElementary' : toSubstructure.IsElementary

variable {L M}

namespace ElementarySubstructure

attribute [coe] toSubstructure

-- INSTANCE (free from Core): instCoe

-- INSTANCE (free from Core): instSetLike

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): inducedStructure
