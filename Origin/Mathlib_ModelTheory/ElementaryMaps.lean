/-
Extracted from ModelTheory/ElementaryMaps.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Elementary Maps Between First-Order Structures

## Main Definitions

- A `FirstOrder.Language.ElementaryEmbedding` is an embedding that commutes with the
  realizations of formulas.
- The `FirstOrder.Language.elementaryDiagram` of a structure is the set of all sentences with
  parameters that the structure satisfies.
- `FirstOrder.Language.ElementaryEmbedding.ofModelsElementaryDiagram` is the canonical
  elementary embedding of any structure into a model of its elementary diagram.

## Main Results

- The Tarski-Vaught Test for embeddings: `FirstOrder.Language.Embedding.isElementary_of_exists`
  gives a simple criterion for an embedding to be elementary.
-/

open FirstOrder

namespace FirstOrder

namespace Language

open Structure

variable (L : Language) (M : Type*) (N : Type*) {P : Type*} {Q : Type*}

variable [L.Structure M] [L.Structure N] [L.Structure P] [L.Structure Q]

structure ElementaryEmbedding where
  /-- The underlying embedding -/
  toFun : M → N
  -- Porting note:
  -- The autoparam here used to be `obviously`.
  -- We have replaced it with `aesop` but that isn't currently sufficient.
  -- See https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Aesop.20and.20cases
  -- If that can be improved, we should remove the proofs below.
  map_formula' :
    ∀ ⦃n⦄ (φ : L.Formula (Fin n)) (x : Fin n → M), φ.Realize (toFun ∘ x) ↔ φ.Realize x := by
    aesop
