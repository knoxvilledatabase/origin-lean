/-
Extracted from GroupTheory/FreeGroup/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Free groups

This file defines free groups over a type. Furthermore, it is shown that the free group construction
is an instance of a monad. For the result that `FreeGroup` is the left adjoint to the forgetful
functor from groups to types, see `Mathlib/Algebra/Category/Grp/Adjunctions.lean`.

## Main definitions

* `FreeGroup`/`FreeAddGroup`: the free group (resp. free additive group) associated to a type
  `α` defined as the words over `a : α × Bool` modulo the relation `a * x * x⁻¹ * b = a * b`.
* `FreeGroup.mk`/`FreeAddGroup.mk`: the canonical quotient map `List (α × Bool) → FreeGroup α`.
* `FreeGroup.of`/`FreeAddGroup.of`: the canonical injection `α → FreeGroup α`.
* `FreeGroup.lift f`/`FreeAddGroup.lift`: the canonical group homomorphism `FreeGroup α →* G`
  given a group `G` and a function `f : α → G`.

## Main statements

* `FreeGroup.Red.church_rosser`/`FreeAddGroup.Red.church_rosser`: The Church-Rosser theorem for word
  reduction (also known as Newman's diamond lemma).
* `FreeGroup.freeGroupUnitEquivInt`: The free group over the one-point type
  is isomorphic to the integers.
* The free group construction is an instance of a monad.

## Implementation details

First we introduce the one step reduction relation `FreeGroup.Red.Step`:
`w * x * x⁻¹ * v   ~>   w * v`, its reflexive transitive closure `FreeGroup.Red.trans`
and prove that its join is an equivalence relation. Then we introduce `FreeGroup α` as a quotient
over `FreeGroup.Red.Step`.

For the additive version we introduce the same relation under a different name so that we can
distinguish the quotient types more easily.


## Tags

free group, Newman's diamond lemma, Church-Rosser theorem
-/

open Relation

open scoped List

universe u v w

variable {α : Type u}

attribute [local simp] List.append_eq_has_append

insert_to_additive_translation FreeGroup FreeAddGroup

inductive FreeAddGroup.Red.Step : List (α × Bool) → List (α × Bool) → Prop
  | not {L₁ L₂ x b} : FreeAddGroup.Red.Step (L₁ ++ (x, b) :: (x, not b) :: L₂) (L₁ ++ L₂)

attribute [simp] FreeAddGroup.Red.Step.not
