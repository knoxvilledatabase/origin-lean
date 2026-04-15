/-
Extracted from Algebra/Group/Action/Pretransitive.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Pretransitive group actions

This file defines a typeclass for pretransitive group actions.

## Notation

- `a • b` is used as notation for `SMul.smul a b`.
- `a +ᵥ b` is used as notation for `VAdd.vadd a b`.

## Implementation details

This file should avoid depending on other parts of `GroupTheory`, to avoid import cycles.
More sophisticated lemmas belong in `GroupTheory.GroupAction`.

## Tags

group action
-/

assert_not_exists MonoidWithZero

open Function (Injective Surjective)

variable {M G α β : Type*}

/-!
### (Pre)transitive action

`M` acts pretransitively on `α` if for any `x y` there is `g` such that `g • x = y` (or `g +ᵥ x = y`
for an additive action). A transitive action should furthermore have `α` nonempty.

In this section we define typeclasses `MulAction.IsPretransitive` and
`AddAction.IsPretransitive` and provide `MulAction.exists_smul_eq`/`AddAction.exists_vadd_eq`,
`MulAction.surjective_smul`/`AddAction.surjective_vadd` as public interface to access this
property. We do not provide typeclasses `*Action.IsTransitive`; users should assume
`[MulAction.IsPretransitive M α] [Nonempty α]` instead.
-/

class AddAction.IsPretransitive (M α : Type*) [VAdd M α] : Prop where
  /-- There is `g` such that `g +ᵥ x = y`. -/
  exists_vadd_eq : ∀ x y : α, ∃ g : M, g +ᵥ x = y
