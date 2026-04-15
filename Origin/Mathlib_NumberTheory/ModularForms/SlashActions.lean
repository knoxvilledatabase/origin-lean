/-
Extracted from NumberTheory/ModularForms/SlashActions.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Slash actions

This file defines a class of slash actions, which are families of right actions of a group on an a
additive monoid, parametrized by some index type. This is modeled on the slash action of
`GL (Fin 2) ℝ` on the space of modular forms.

## Notation

Scoped in the `ModularForm` namespace, this file defines

* `f ∣[k] A`: the `k`th slash action by `A` on `f`
-/

open Complex UpperHalfPlane ModularGroup

open scoped MatrixGroups

class SlashAction (β G α : Type*) [Monoid G] [AddMonoid α] where
  map : β → G → α → α
  zero_slash : ∀ (k : β) (g : G), map k g 0 = 0
  slash_one : ∀ (k : β) (a : α), map k 1 a = a
  slash_mul : ∀ (k : β) (g h : G) (a : α), map k (g * h) a = map k h (map k g a)
  add_slash : ∀ (k : β) (g : G) (a b : α), map k g (a + b) = map k g a + map k g b

scoped[ModularForm] notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

open scoped ModularForm
