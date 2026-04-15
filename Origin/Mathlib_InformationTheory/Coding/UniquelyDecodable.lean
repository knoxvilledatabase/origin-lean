/-
Extracted from InformationTheory/Coding/UniquelyDecodable.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Uniquely Decodable Codes

This file defines uniquely decodable codes and proves basic properties.

## Main definitions

* `UniquelyDecodable`: A set of codewords is uniquely decodable if distinct concatenations
  of codewords yield distinct strings.

## Main results

* `UniquelyDecodable.epsilon_not_mem`: Uniquely decodable codes cannot contain the empty
  string.
* `UniquelyDecodable.flatten_injective`: The flatten function is injective on lists of
  codewords from a uniquely decodable code.
-/

namespace InformationTheory

variable {α : Type*}

def UniquelyDecodable (S : Set (List α)) : Prop :=
  ∀ (L₁ L₂ : List (List α)),
    (∀ w ∈ L₁, w ∈ S) → (∀ w ∈ L₂, w ∈ S) →
    L₁.flatten = L₂.flatten → L₁ = L₂

variable {S : Set (List α)}

lemma UniquelyDecodable.epsilon_not_mem
    (h : UniquelyDecodable S) :
    [] ∉ S := by
  simpa using h [[]] [[], []]

lemma UniquelyDecodable.flatten_injective (h : UniquelyDecodable S) :
    Function.Injective (fun (L : {L : List (List α) // ∀ x ∈ L, x ∈ S}) => L.val.flatten) := by
  intro L₁ L₂ hflat
  apply Subtype.ext
  exact h L₁.val L₂.val L₁.prop L₂.prop hflat

end InformationTheory
