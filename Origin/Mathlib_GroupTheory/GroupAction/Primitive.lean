/-
Extracted from GroupTheory/GroupAction/Primitive.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Primitive actions

## Definitions

- `MulAction.IsPreprimitive G X`
  A structure that says that the action of a type `G` on a type `X`
  (defined by an instance `SMul G X`) is *preprimitive*,
  namely, it is pretransitive and the only blocks are ⊤ and subsingletons.
  (The pretransitivity assumption is essentially trivial,
  because orbits are blocks, unless the action itself is trivial.)

  The notion which is introduced in classical books on group theory
  is restricted to group actions.
  In fact, it may be irrelevant if the action is degenerate,
  when “trivial blocks” might not be blocks.
  Moreover, the classical notion is *primitive*,
  which further assumes that `X` is not empty.

- `MulAction.IsQuasiPreprimitive G X`
  A structure that says that the action of the group `G` on the type `X` is *quasipreprimitive*,
  namely, normal subgroups of `G` which act nontrivially act pretransitively.

- We prove some straightforward theorems that relate preprimitivity
  under equivariant maps, for images and preimages.

## Relation with stabilizers

- `MulAction.isSimpleOrderBlockMem_iff_isPreprimitive`
  relates primitivity and the fact that the inclusion order on blocks containing is simple.

- `MulAction.isCoatom_stabilizer_iff_preprimitive`
  An action is preprimitive iff the stabilizers of points are maximal subgroups.

- `MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive`
  Stabilizers of points under a preprimitive action are maximal subgroups.

## Relation with normal subgroups

- `MulAction.IsPreprimitive.isQuasipreprimitive`
  Preprimitive actions are quasipreprimitive.

## Particular results for actions on finite types

- `MulAction.IsPreprimitive.of_prime_card` :
  A pretransitive action on a finite type of prime cardinal is preprimitive.

- `MulAction.IsPreprimitive.of_card_lt`
  Given an equivariant map from a preprimitive action,
  if the image is at least twice the codomain, then the codomain is preprimitive.

- `MulAction.IsPreprimitive.exists_mem_smul_and_notMem_smul` : **Theorem of Rudio**.
  For a preprimitive action, a subset which is neither empty nor full has a translate
  which contains a given point and avoids another one.

-/

open Pointwise

namespace MulAction

variable (G : Type*) (X : Type*)

class _root_.AddAction.IsPreprimitive [VAdd G X] : Prop extends AddAction.IsPretransitive G X where
  /-- An action is preprimitive if it is pretransitive and
  the only blocks are the trivial ones -/
  isTrivialBlock_of_isBlock : ∀ {B : Set X}, AddAction.IsBlock G B → AddAction.IsTrivialBlock B
