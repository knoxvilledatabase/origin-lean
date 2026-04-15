/-
Extracted from Data/List/Pairwise.lean
Genuine: 11 of 11 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Pairwise relations on a list

This file provides basic results about `List.Pairwise` and `List.pwFilter` (definitions are in
`Data.List.Defs`).
`Pairwise R [a 0, ..., a (n - 1)]` means `∀ i j, i < j → R (a i) (a j)`. For example,
`Pairwise (≠) l` means that all elements of `l` are distinct, and `Pairwise (<) l` means that `l`
is strictly increasing.
`pwFilter R l` is the list obtained by iteratively adding each element of `l` that doesn't break
the pairwiseness of the list we have so far. It thus yields `l'` a maximal sublist of `l` such that
`Pairwise R l'`.

## Tags

sorted, nodup
-/

open Nat Function

namespace List

variable {α β : Type*} {R : α → α → Prop} {l : List α} {a : α}

mk_iff_of_inductive_prop List.Pairwise List.pairwise_iff

/-! ### Pairwise -/

theorem Pairwise.forall_of_forall (H : Symmetric R) (H₁ : ∀ x ∈ l, R x x) (H₂ : l.Pairwise R) :
    ∀ ⦃x⦄, x ∈ l → ∀ ⦃y⦄, y ∈ l → R x y :=
  H₂.forall_of_forall_of_flip H₁ <| by rwa [H.flip_eq]

theorem Pairwise.forall (hR : Symmetric R) (hl : l.Pairwise R) :
    ∀ ⦃a⦄, a ∈ l → ∀ ⦃b⦄, b ∈ l → a ≠ b → R a b := by
  apply Pairwise.forall_of_forall
  · exact fun a b h hne => hR (h hne.symm)
  · exact fun _ _ hx => (hx rfl).elim
  · exact hl.imp (@fun a b h _ => by exact h)

theorem Pairwise.set_pairwise (hl : Pairwise R l) (hr : Symmetric R) : { x | x ∈ l }.Pairwise R :=
  hl.forall hr

theorem pairwise_of_reflexive_of_forall_ne [Std.Refl R] (h : ∀ a ∈ l, ∀ b ∈ l, a ≠ b → R a b) :
    l.Pairwise R := by
  rw [pairwise_iff_forall_sublist]
  intro a b hab
  if heq : a = b then
    cases heq; apply refl
  else
    apply h <;> try (apply hab.subset; simp)
    exact heq

theorem Pairwise.rel_head_tail (h₁ : l.Pairwise R) (ha : a ∈ l.tail) :
    R (l.head <| ne_nil_of_mem <| mem_of_mem_tail ha) a := by
  grind +splitIndPred

theorem Pairwise.rel_head_of_rel_head_head (h₁ : l.Pairwise R) (ha : a ∈ l)
    (hhead : R (l.head <| ne_nil_of_mem ha) (l.head <| ne_nil_of_mem ha)) :
    R (l.head <| ne_nil_of_mem ha) a := by
  grind +splitIndPred

theorem Pairwise.rel_head [Std.Refl R] (h₁ : l.Pairwise R) (ha : a ∈ l) :
    R (l.head <| ne_nil_of_mem ha) a :=
  h₁.rel_head_of_rel_head_head ha (refl_of ..)

theorem Pairwise.rel_dropLast_getLast (h : l.Pairwise R) (ha : a ∈ l.dropLast) :
    R a (l.getLast <| ne_nil_of_mem <| dropLast_subset _ ha) := by
  rw [← pairwise_reverse] at h
  rw [getLast_eq_head_reverse]
  exact h.rel_head_tail (by rwa [tail_reverse, mem_reverse])

theorem Pairwise.rel_getLast_of_rel_getLast_getLast (h₁ : l.Pairwise R) (ha : a ∈ l)
    (hlast : R (l.getLast <| ne_nil_of_mem ha) (l.getLast <| ne_nil_of_mem ha)) :
    R a (l.getLast <| ne_nil_of_mem ha) := by
  rw [← dropLast_concat_getLast (ne_nil_of_mem ha), mem_append, List.mem_singleton] at ha
  exact ha.elim h₁.rel_dropLast_getLast (· ▸ hlast)

theorem Pairwise.rel_getLast [Std.Refl R] (h₁ : l.Pairwise R) (ha : a ∈ l) :
    R a (l.getLast <| ne_nil_of_mem ha) :=
  h₁.rel_getLast_of_rel_getLast_getLast ha (refl_of ..)

protected alias ⟨Pairwise.of_reverse, Pairwise.reverse⟩ := pairwise_reverse

theorem Pairwise.head!_le [Inhabited α] [Std.Refl R] (h : l.Pairwise R)
    (ha : a ∈ l) : R l.head! a := by
  cases l
  · contradiction
  · cases ha with
    | head => exact refl_of ..
    | tail => exact rel_of_pairwise_cons h (by assumption)
