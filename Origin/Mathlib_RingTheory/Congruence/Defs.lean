/-
Extracted from RingTheory/Congruence/Defs.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Congruence relations on rings

This file defines congruence relations on rings, which extend `Con` and `AddCon` on monoids and
additive monoids.

Most of the time you likely want to use the `Ideal.Quotient` API that is built on top of this.

## Main Definitions

* `RingCon R`: the type of congruence relations respecting `+` and `*`.
* `RingConGen r`: the inductively defined smallest ring congruence relation containing a given
  binary relation.

## TODO

* Use this for `RingQuot` too.
* Copy across more API from `Con` and `AddCon` in `Mathlib/GroupTheory/Congruence/`.
-/

open Function

structure RingCon (R : Type*) [Add R] [Mul R] extends Con R, AddCon R where

add_decl_doc RingCon.toCon

add_decl_doc RingCon.toAddCon

variable {R : Type*}

inductive RingConGen.Rel [Add R] [Mul R] (r : R → R → Prop) : R → R → Prop
  | of : ∀ x y, r x y → RingConGen.Rel r x y
  | refl : ∀ x, RingConGen.Rel r x x
  | symm : ∀ {x y}, RingConGen.Rel r x y → RingConGen.Rel r y x
  | trans : ∀ {x y z}, RingConGen.Rel r x y → RingConGen.Rel r y z → RingConGen.Rel r x z
  | add : ∀ {w x y z}, RingConGen.Rel r w x → RingConGen.Rel r y z →
      RingConGen.Rel r (w + y) (x + z)
  | mul : ∀ {w x y z}, RingConGen.Rel r w x → RingConGen.Rel r y z →
      RingConGen.Rel r (w * y) (x * z)

def ringConGen [Add R] [Mul R] (r : R → R → Prop) : RingCon R where
  r := RingConGen.Rel r
  iseqv := ⟨RingConGen.Rel.refl, @RingConGen.Rel.symm _ _ _ _, @RingConGen.Rel.trans _ _ _ _⟩
  add' := RingConGen.Rel.add
  mul' := RingConGen.Rel.mul

namespace RingCon

section Basic

variable [Add R] [Mul R] {c d : RingCon R}

lemma toCon_injective : Injective fun c : RingCon R ↦ c.toCon := fun c d ↦ by cases c; congr!
