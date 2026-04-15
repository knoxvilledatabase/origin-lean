/-
Extracted from Data/Fintype/EquivFin.lean
Genuine: 10 of 11 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Equivalences between `Fintype`, `Fin` and `Finite`

This file defines the bijection between a `Fintype α` and `Fin (Fintype.card α)`, and uses this to
relate `Fintype` with `Finite`. From that we can derive properties of `Finite` and `Infinite`,
and show some instances of `Infinite`.

## Main declarations

* `Fintype.truncEquivFin`: A fintype `α` is computably equivalent to `Fin (card α)`. The
  `Trunc`-free, noncomputable version is `Fintype.equivFin`.
* `Fintype.truncEquivOfCardEq` `Fintype.equivOfCardEq`: Two fintypes of same cardinality are
  equivalent. See above.
* `Fin.equiv_iff_eq`: `Fin m ≃ Fin n` iff `m = n`.
* `Infinite.natEmbedding`: An embedding of `ℕ` into an infinite type.

Types which have an injection from/a surjection to an `Infinite` type are themselves `Infinite`.
See `Infinite.of_injective` and `Infinite.of_surjective`.

## Instances

We provide `Infinite` instances for
* specific types: `ℕ`, `ℤ`, `String`
* type constructors: `Multiset α`, `List α`

-/

assert_not_exists Monoid

open Function

universe u v

variable {α β γ : Type*}

open Finset

namespace Fintype

def truncEquivFin (α) [DecidableEq α] [Fintype α] : Trunc (α ≃ Fin (card α)) := by
  unfold card Finset.card
  exact
    Quot.recOnSubsingleton
      (motive := fun s : Multiset α =>
        (∀ x : α, x ∈ s) → s.Nodup → Trunc (α ≃ Fin (Multiset.card s)))
      univ.val
      (fun l (h : ∀ x : α, x ∈ l) (nd : l.Nodup) => Trunc.mk (nd.getEquivOfForallMemList _ h).symm)
      mem_univ_val univ.2

noncomputable def equivFin (α) [Fintype α] : α ≃ Fin (card α) :=
  letI := Classical.decEq α
  (truncEquivFin α).out

def truncFinBijection (α) [Fintype α] : Trunc { f : Fin (card α) → α // Bijective f } := by
  unfold card Finset.card
  refine
    Quot.recOnSubsingleton
      (motive := fun s : Multiset α =>
        (∀ x : α, x ∈ s) → s.Nodup → Trunc {f : Fin (Multiset.card s) → α // Bijective f})
      univ.val
      (fun l (h : ∀ x : α, x ∈ l) (nd : l.Nodup) => Trunc.mk (nd.getBijectionOfForallMemList _ h))
      mem_univ_val univ.2

end Fintype

namespace Fintype

variable [Fintype α] [Fintype β]

def truncEquivFinOfCardEq [DecidableEq α] {n : ℕ} (h : Fintype.card α = n) : Trunc (α ≃ Fin n) :=
  (truncEquivFin α).map fun e => e.trans (finCongr h)

noncomputable def equivFinOfCardEq {n : ℕ} (h : Fintype.card α = n) : α ≃ Fin n :=
  letI := Classical.decEq α
  (truncEquivFinOfCardEq h).out

def truncEquivOfCardEq [DecidableEq α] [DecidableEq β] (h : card α = card β) : Trunc (α ≃ β) :=
  (truncEquivFinOfCardEq h).bind fun e => (truncEquivFin β).map fun e' => e.trans e'.symm

noncomputable def equivOfCardEq (h : card α = card β) : α ≃ β := by
  letI := Classical.decEq α
  letI := Classical.decEq β
  exact (truncEquivOfCardEq h).out

end

theorem card_eq {α β} [_F : Fintype α] [_G : Fintype β] : card α = card β ↔ Nonempty (α ≃ β) :=
  ⟨fun h =>
    haveI := Classical.propDecidable
    (truncEquivOfCardEq h).nonempty,
    fun ⟨f⟩ => card_congr f⟩

end Fintype

/-!
### Relation to `Finite`

In this section we prove that `α : Type*` is `Finite` if and only if `Fintype α` is nonempty.
-/

protected theorem Fintype.finite {α : Type*} (_inst : Fintype α) : Finite α :=
  ⟨Fintype.equivFin α⟩

set_option linter.unusedFintypeInType false in

-- INSTANCE (free from Core): (priority

theorem finite_iff_nonempty_fintype (α : Type*) : Finite α ↔ Nonempty (Fintype α) :=
  ⟨fun _ => nonempty_fintype α, fun ⟨_⟩ => inferInstance⟩
