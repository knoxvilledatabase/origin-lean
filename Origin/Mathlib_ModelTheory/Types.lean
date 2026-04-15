/-
Extracted from ModelTheory/Types.lean
Genuine: 8 of 10 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Type Spaces

This file defines the space of complete types over a first-order theory.
(Note that types in model theory are different from types in type theory.)

## Main Definitions

- `FirstOrder.Language.Theory.CompleteType`:
  `T.CompleteType α` consists of complete types over the theory `T` with variables `α`.
- `FirstOrder.Language.Theory.typeOf` is the type of a given tuple.
- `FirstOrder.Language.Theory.realizedTypes`: `T.realizedTypes M α` is the set of
  types in `T.CompleteType α` that are realized in `M` - that is, the type of some tuple in `M`.

## Main Results

- `FirstOrder.Language.Theory.CompleteType.nonempty_iff`:
  The space `T.CompleteType α` is nonempty exactly when `T` is satisfiable.
- `FirstOrder.Language.Theory.CompleteType.exists_modelType_is_realized_in`: Every type is realized
  in some model.

## Implementation Notes

- Complete types are implemented as maximal consistent theories in an expanded language.
  More frequently they are described as maximal consistent sets of formulas, but this is equivalent.

## TODO

- Connect `T.CompleteType α` to sets of formulas `L.Formula α`.
-/

universe u v w w'

open Cardinal Set FirstOrder

namespace FirstOrder

namespace Language

namespace Theory

variable {L : Language.{u, v}} (T : L.Theory) (α : Type w)

structure CompleteType where
  /-- The underlying theory -/
  toTheory : L[[α]].Theory
  subset' : (L.lhomWithConstants α).onTheory T ⊆ toTheory
  isMaximal' : toTheory.IsMaximal

variable {α}

def typesWith (T : L.Theory) : L[[α]].Sentence → Set (CompleteType T α) :=
  fun φ ↦ {p | φ ∈ p.toTheory}

variable {T}

namespace CompleteType

attribute [coe] CompleteType.toTheory

-- INSTANCE (free from Core): Sentence.instSetLike

-- INSTANCE (free from Core): :

theorem isMaximal (p : T.CompleteType α) : IsMaximal (p : L[[α]].Theory) :=
  p.isMaximal'

theorem subset (p : T.CompleteType α) : (L.lhomWithConstants α).onTheory T ⊆ (p : L[[α]].Theory) :=
  p.subset'

theorem mem_or_not_mem (p : T.CompleteType α) (φ : L[[α]].Sentence) : φ ∈ p ∨ φ.not ∈ p :=
  p.isMaximal.mem_or_not_mem φ

lemma false_of_mem_of_not_mem (hT : T.IsSatisfiable) {φ : L.Sentence} (hφ : φ ∈ T) (hφ' : ∼φ ∈ T) :
    False :=
  have ⟨M⟩ := hT
  (M.is_model.realize_of_mem _ hφ') (M.is_model.realize_of_mem _ hφ)

theorem mem_of_models (p : T.CompleteType α) {φ : L[[α]].Sentence}
    (h : (L.lhomWithConstants α).onTheory T ⊨ᵇ φ) : φ ∈ p :=
  (p.mem_or_not_mem φ).resolve_right fun con =>
    ((models_iff_not_satisfiable _).1 h)
      (p.isMaximal.1.mono (union_subset p.subset (singleton_subset_iff.2 con)))

theorem not_mem_iff (p : T.CompleteType α) (φ : L[[α]].Sentence) : φ.not ∈ p ↔ φ ∉ p :=
  ⟨fun hf ht => by
    have h : ¬IsSatisfiable ({φ, φ.not} : L[[α]].Theory) := by
      rintro ⟨@⟨_, _, h, _⟩⟩
      simp only [model_iff, mem_insert_iff, mem_singleton_iff, forall_eq_or_imp, forall_eq] at h
      exact h.2 h.1
    refine h (p.isMaximal.1.mono ?_)
    rw [insert_subset_iff, singleton_subset_iff]
    exact ⟨ht, hf⟩, (p.mem_or_not_mem φ).resolve_left⟩
