/-
Extracted from ModelTheory/Encoding.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Encodings and Cardinality of First-Order Syntax

## Main Definitions

- `FirstOrder.Language.Term.encoding` encodes terms as lists.
- `FirstOrder.Language.BoundedFormula.encoding` encodes bounded formulas as lists.

## Main Results

- `FirstOrder.Language.Term.card_le` shows that the number of terms in `L.Term α` is at most
  `max ℵ₀ # (α ⊕ Σ i, L.Functions i)`.
- `FirstOrder.Language.BoundedFormula.card_le` shows that the number of bounded formulas in
  `Σ n, L.BoundedFormula α n` is at most
  `max ℵ₀ (Cardinal.lift.{max u v} #α + Cardinal.lift.{u'} L.card)`.

## TODO

- `Primcodable` instances for terms and formulas, based on the `encoding`s
- Computability facts about term and formula operations, to set up a computability approach to
  incompleteness

-/

universe u v w u'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

variable {α : Type u'}

open FirstOrder Cardinal

open Computability List Structure Fin

namespace Term

def listEncode : L.Term α → List (α ⊕ (Σ i, L.Functions i))
  | var i => [Sum.inl i]
  | func f ts =>
    Sum.inr (⟨_, f⟩ : Σ i, L.Functions i)::(List.finRange _).flatMap fun i => (ts i).listEncode

def listDecode : List (α ⊕ (Σ i, L.Functions i)) → List (L.Term α)
  | [] => []
  | Sum.inl a::l => (var a)::listDecode l
  | Sum.inr ⟨n, f⟩::l =>
    if h : n ≤ (listDecode l).length then
      (func f (fun i => (listDecode l)[i])) :: (listDecode l).drop n
    else []

theorem listDecode_encode_list (l : List (L.Term α)) :
    listDecode (l.flatMap listEncode) = l := by
  suffices h : ∀ (t : L.Term α) (l : List (α ⊕ (Σ i, L.Functions i))),
      listDecode (t.listEncode ++ l) = t::listDecode l by
    induction l with
    | nil => rfl
    | cons t l lih => rw [flatMap_cons, h t (l.flatMap listEncode), lih]
  intro t l
  induction t generalizing l with
  | var => rw [listEncode, singleton_append, listDecode]
  | @func n f ts ih =>
    rw [listEncode, cons_append, listDecode]
    have h : listDecode (((finRange n).flatMap fun i : Fin n => (ts i).listEncode) ++ l) =
        (finRange n).map ts ++ listDecode l := by
      induction finRange n with
      | nil => rfl
      | cons i l' l'ih => rw [flatMap_cons, List.append_assoc, ih, map_cons, l'ih, cons_append]
    simp only [h, length_append, length_map, length_finRange, le_add_iff_nonneg_right,
      _root_.zero_le, ↓reduceDIte, getElem_fin, cons.injEq, func.injEq, heq_eq_eq, true_and]
    refine ⟨funext (fun i => ?_), ?_⟩
    · simp only [length_map, length_finRange, is_lt, getElem_append_left, getElem_map,
      getElem_finRange, cast_mk, Fin.eta]
    · simp only [length_map, length_finRange, drop_left']
