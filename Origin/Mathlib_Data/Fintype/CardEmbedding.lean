/-
Extracted from Data/Fintype/CardEmbedding.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Number of embeddings

This file establishes the cardinality of `α ↪ β` in full generality.
-/

local notation "|" x "|" => Finset.card x

local notation "‖" x "‖" => Fintype.card x

open Function

open Nat

namespace Fintype

theorem card_embedding_eq_of_unique {α β : Type*} [Unique α] [Fintype β] [Fintype (α ↪ β)] :
    ‖α ↪ β‖ = ‖β‖ :=
  card_congr Equiv.uniqueEmbeddingEquivResult
