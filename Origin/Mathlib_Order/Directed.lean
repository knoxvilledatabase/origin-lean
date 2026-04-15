/-
Extracted from Order/Directed.lean
Genuine: 14 of 18 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Directed indexed families and sets

This file defines directed indexed families and directed sets. An indexed family/set is
directed iff each pair of elements has a shared upper bound.

## Main declarations

* `Directed r f`: Predicate stating that the indexed family `f` is `r`-directed.
* `DirectedOn r s`: Predicate stating that the set `s` is `r`-directed.
* `IsDirected α r`: Prop-valued mixin stating that `α` is `r`-directed. Follows the style of the
  unbundled relation classes such as `Std.Total`.

## TODO

Define connected orders (the transitive symmetric closure of `≤` is everything) and show that
(co)directed orders are connected.

## References
* [Gierz et al, *A Compendium of Continuous Lattices*][GierzEtAl1980]
-/

open Function

universe u v w

variable {α : Type u} {β : Type v} {ι : Sort w} (r r' s : α → α → Prop)

local infixl:50 " ≼ " => r

def Directed (f : ι → α) :=
  ∀ x y, ∃ z, f x ≼ f z ∧ f y ≼ f z

def DirectedOn (s : Set α) :=
  ∀ x ∈ s, ∀ y ∈ s, ∃ z ∈ s, x ≼ z ∧ y ≼ z

variable {r r'}

theorem directedOn_iff_directed {s} : @DirectedOn α r s ↔ Directed r (Subtype.val : s → α) := by
  simp only [DirectedOn, Directed, Subtype.exists, exists_and_left, exists_prop, Subtype.forall]
  exact forall₂_congr fun x _ => by simp [And.comm, and_assoc]

alias ⟨DirectedOn.directed_val, _⟩ := directedOn_iff_directed

theorem directedOn_range {f : ι → α} : Directed r f ↔ DirectedOn r (Set.range f) := by
  simp_rw [Directed, DirectedOn, Set.forall_mem_range, Set.exists_range_iff]

protected alias ⟨Directed.directedOn_range, _⟩ := directedOn_range

theorem directedOn_image {s : Set β} {f : β → α} :
    DirectedOn r (f '' s) ↔ DirectedOn (f ⁻¹'o r) s := by
  simp only [DirectedOn, Set.mem_image, exists_exists_and_eq_and, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, Order.Preimage]

theorem DirectedOn.mono' {s : Set α} (hs : DirectedOn r s)
    (h : ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → r a b → r' a b) : DirectedOn r' s := fun _ hx _ hy =>
  let ⟨z, hz, hxz, hyz⟩ := hs _ hx _ hy
  ⟨z, hz, h hx hz hxz, h hy hz hyz⟩

theorem Directed.mono_comp (r : α → α → Prop) {ι} {rb : β → β → Prop} {g : α → β} {f : ι → α}
    (hg : ∀ ⦃x y⦄, r x y → rb (g x) (g y)) (hf : Directed r f) : Directed rb (g ∘ f) :=
  directed_comp.2 <| hf.mono hg

theorem DirectedOn.mono_comp {r : α → α → Prop} {rb : β → β → Prop} {g : α → β} {s : Set α}
    (hg : ∀ ⦃x y⦄, r x y → rb (g x) (g y)) (hf : DirectedOn r s) : DirectedOn rb (g '' s) :=
  directedOn_image.mpr (hf.mono hg)

theorem directedOn_of_sup_mem [SemilatticeSup α] {S : Set α}
    (H : ∀ ⦃i j⦄, i ∈ S → j ∈ S → i ⊔ j ∈ S) : DirectedOn (· ≤ ·) S := fun a ha b hb =>
  ⟨a ⊔ b, H ha hb, le_sup_left, le_sup_right⟩

theorem Directed.extend_bot [Preorder α] [OrderBot α] {e : ι → β} {f : ι → α}
    (hf : Directed (· ≤ ·) f) (he : Function.Injective e) :
    Directed (· ≤ ·) (Function.extend e f ⊥) := by
  intro a b
  rcases (em (∃ i, e i = a)).symm with (ha | ⟨i, rfl⟩)
  · use b
    simp [Function.extend_apply' _ _ _ ha]
  rcases (em (∃ i, e i = b)).symm with (hb | ⟨j, rfl⟩)
  · use e i
    simp [Function.extend_apply' _ _ _ hb]
  rcases hf i j with ⟨k, hi, hj⟩
  use e k
  simp only [he.extend_apply, *, true_and]

theorem directedOn_of_inf_mem [SemilatticeInf α] {S : Set α}
    (H : ∀ ⦃i j⦄, i ∈ S → j ∈ S → i ⊓ j ∈ S) : DirectedOn (· ≥ ·) S :=
  directedOn_of_sup_mem (α := αᵒᵈ) H

theorem Std.Total.directed [Std.Total r] (f : ι → α) : Directed r f := fun i j =>
  Or.casesOn (total_of r (f i) (f j)) (fun h => ⟨j, h, refl _⟩) fun h => ⟨i, refl _, h⟩

theorem Std.Total.directedOn [Std.Total r] (s : Set α) : DirectedOn r s := fun a ha b hb =>
  Or.casesOn (total_of r a b) (fun h => ⟨b, hb, h, refl _⟩) fun h => ⟨a, ha, refl _, h⟩

class IsDirected (α : Type*) (r : α → α → Prop) : Prop where
  /-- For every pair of elements `a` and `b` there is a `c` such that `r a c` and `r b c` -/
  directed (a b : α) : ∃ c, r a c ∧ r b c
