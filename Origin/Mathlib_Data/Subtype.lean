/-
Extracted from Data/Subtype.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Subtypes

This file provides basic API for subtypes, which are defined in core.

A subtype is a type made from restricting another type, say `α`, to its elements that satisfy some
predicate, say `p : α → Prop`. Specifically, it is the type of pairs `⟨val, property⟩` where
`val : α` and `property : p val`. It is denoted `Subtype p` and notation `{val : α // p val}` is
available.

A subtype has a natural coercion to the parent type, by coercing `⟨val, property⟩` to `val`. As
such, subtypes can be thought of as bundled sets, the difference being that elements of a set are
still of type `α` while elements of a subtype aren't.
-/

open Function

namespace Subtype

variable {α β γ : Sort*} {p q : α → Prop}

attribute [coe] Subtype.val

initialize_simps_projections Subtype (val → coe)

theorem prop (x : Subtype p) : p x :=
  x.2

protected theorem forall' {q : ∀ x, p x → Prop} : (∀ x h, q x h) ↔ ∀ x : { a // p a }, q x x.2 :=
  (@Subtype.forall _ _ fun x ↦ q x.1 x.2).symm

protected theorem exists' {q : ∀ x, p x → Prop} : (∃ x h, q x h) ↔ ∃ x : { a // p a }, q x x.2 :=
  (@Subtype.exists _ _ fun x ↦ q x.1 x.2).symm

theorem heq_iff_coe_eq (h : ∀ x, p x ↔ q x) {a1 : { x // p x }} {a2 : { x // q x }} :
    a1 ≍ a2 ↔ (a1 : α) = (a2 : α) :=
  Eq.rec
    (motive := fun (pp : (α → Prop)) _ ↦ ∀ a2' : {x // pp x}, a1 ≍ a2' ↔ (a1 : α) = (a2' : α))
    (by grind) (funext <| fun x ↦ propext (h x)) a2

lemma heq_iff_coe_heq {α β : Sort _} {p : α → Prop} {q : β → Prop} {a : {x // p x}}
    {b : {y // q y}} (h : α = β) (h' : p ≍ q) : a ≍ b ↔ (a : α) ≍ (b : β) := by grind
