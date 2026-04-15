/-
Extracted from GroupTheory/Perm/Cycle/Concrete.lean
Genuine: 7 of 7 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Properties of cyclic permutations constructed from lists/cycles

In the following, `{α : Type*} [Fintype α] [DecidableEq α]`.

## Main definitions

* `Cycle.formPerm`: the cyclic permutation created by looping over a `Cycle α`
* `Equiv.Perm.toList`: the list formed by iterating application of a permutation
* `Equiv.Perm.toCycle`: the cycle formed by iterating application of a permutation
* `Equiv.Perm.isoCycle`: the equivalence between cyclic permutations `f : Perm α`
  and the terms of `Cycle α` that correspond to them
* `Equiv.Perm.isoCycle'`: the same equivalence as `Equiv.Perm.isoCycle`
  but with evaluation via choosing over fintypes
* The notation `c[1, 2, 3]` to emulate notation of cyclic permutations `(1 2 3)`
* A `Repr` instance for any `Perm α`, by representing the `Finset` of
  `Cycle α` that correspond to the cycle factors.

## Main results

* `List.isCycle_formPerm`: a nontrivial list without duplicates, when interpreted as
  a permutation, is cyclic
* `Equiv.Perm.IsCycle.existsUnique_cycle`: there is only one nontrivial `Cycle α`
  corresponding to each cyclic `f : Perm α`

## Implementation details

The forward direction of `Equiv.Perm.isoCycle'` uses `Fintype.choose` of the uniqueness
result, relying on the `Fintype` instance of a `Cycle.Nodup` subtype.
It is unclear if this works faster than the `Equiv.Perm.toCycle`, which relies
on recursion over `Finset.univ`.

-/

open Equiv Equiv.Perm List

variable {α : Type*}

namespace List

variable [DecidableEq α] {l l' : List α}

theorem formPerm_disjoint_iff (hl : Nodup l) (hl' : Nodup l') (hn : 2 ≤ l.length)
    (hn' : 2 ≤ l'.length) : Perm.Disjoint (formPerm l) (formPerm l') ↔ l.Disjoint l' := by
  rw [disjoint_iff_eq_or_eq, List.Disjoint]
  constructor
  · rintro h x hx hx'
    specialize h x
    rw [formPerm_apply_mem_eq_self_iff _ hl _ hx, formPerm_apply_mem_eq_self_iff _ hl' _ hx'] at h
    lia
  · intro h x
    by_cases hx : x ∈ l
    on_goal 1 => by_cases hx' : x ∈ l'
    · exact (h hx hx').elim
    all_goals have := List.formPerm_apply_of_notMem ‹_›; tauto

theorem isCycle_formPerm (hl : Nodup l) (hn : 2 ≤ l.length) : IsCycle (formPerm l) := by
  rcases l with - | ⟨x, l⟩
  · norm_num at hn
  induction l generalizing x with
  | nil => norm_num at hn
  | cons y l =>
    use x
    constructor
    · rwa [formPerm_apply_mem_ne_self_iff _ hl _ mem_cons_self]
    · intro w hw
      have : w ∈ x::y::l := mem_of_formPerm_apply_ne hw
      obtain ⟨k, hk, rfl⟩ := getElem_of_mem this
      use k
      simp only [zpow_natCast, formPerm_pow_apply_head _ _ hl k, Nat.mod_eq_of_lt hk]

theorem pairwise_sameCycle_formPerm (hl : Nodup l) (hn : 2 ≤ l.length) :
    Pairwise l.formPerm.SameCycle l :=
  Pairwise.imp_mem.mpr
    (pairwise_of_forall fun _ _ hx hy =>
      (isCycle_formPerm hl hn).sameCycle ((formPerm_apply_mem_ne_self_iff _ hl _ hx).mpr hn)
        ((formPerm_apply_mem_ne_self_iff _ hl _ hy).mpr hn))

theorem cycleOf_formPerm (hl : Nodup l) (hn : 2 ≤ l.length) (x) :
    cycleOf l.attach.formPerm x = l.attach.formPerm :=
  have hn : 2 ≤ l.attach.length := by rwa [← length_attach] at hn
  have hl : l.attach.Nodup := by rwa [← nodup_attach] at hl
  (isCycle_formPerm hl hn).cycleOf_eq
    ((formPerm_apply_mem_ne_self_iff _ hl _ (mem_attach _ _)).mpr hn)

theorem cycleType_formPerm (hl : Nodup l) (hn : 2 ≤ l.length) :
    cycleType l.attach.formPerm = {l.length} := by
  rw [← length_attach] at hn
  rw [← nodup_attach] at hl
  rw [cycleType_eq [l.attach.formPerm]]
  · simp only [map, Function.comp_apply]
    rw [support_formPerm_of_nodup _ hl, card_toFinset, dedup_eq_self.mpr hl]
    · simp
    · intro x h
      simp [h] at hn
  · simp
  · simpa using isCycle_formPerm hl hn
  · simp

theorem formPerm_apply_mem_eq_next (hl : Nodup l) (x : α) (hx : x ∈ l) :
    formPerm l x = next l x hx := by
  obtain ⟨k, hk, rfl⟩ := getElem_of_mem hx
  rw [next_getElem _ hl, formPerm_apply_getElem _ hl]

end List

namespace Cycle

variable [DecidableEq α] (s : Cycle α)

def formPerm : ∀ s : Cycle α, Nodup s → Equiv.Perm α :=
  fun s => Quotient.hrecOn s (fun l _ => List.formPerm l) fun l₁ l₂ (h : l₁ ~r l₂) => by
    apply Function.hfunext
    · ext
      exact h.nodup_iff
    · intro h₁ h₂ _
      exact heq_of_eq (formPerm_eq_of_isRotated h₁ h)
