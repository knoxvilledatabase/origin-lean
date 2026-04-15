/-
Extracted from Order/Antisymmetrization.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Turning a preorder into a partial order

This file allows to make a preorder into a partial order by quotienting out the elements `a`, `b`
such that `a ≤ b` and `b ≤ a`.

`Antisymmetrization` is a functor from `Preorder` to `PartialOrder`. See `Preorder_to_PartialOrder`.

## Main declarations

* `AntisymmRel`: The antisymmetrization relation. `AntisymmRel r a b` means that `a` and `b` are
  related both ways by `r`.
* `Antisymmetrization α r`: The quotient of `α` by `AntisymmRel r`. Even when `r` is just a
  preorder, `Antisymmetrization α` is a partial order.
-/

open Function OrderDual

variable {α β : Type*} {a b c d : α}

section Relation

variable (r : α → α → Prop)

def AntisymmRel (a b : α) : Prop :=
  r a b ∧ r b a

theorem antisymmRel_swap : AntisymmRel (swap r) = AntisymmRel r :=
  funext₂ fun _ _ ↦ propext and_comm

theorem antisymmRel_swap_apply : AntisymmRel (swap r) a b ↔ AntisymmRel r a b :=
  and_comm
