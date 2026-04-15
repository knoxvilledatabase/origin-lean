/-
Extracted from Data/Fintype/Quotient.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Quotients of families indexed by a finite type

This file proves some basic facts and defines lifting and recursion principle for quotients indexed
by a finite type.

## Main definitions

* `Quotient.finChoice`: Given a function `f : Π i, Quotient (S i)` on a fintype `ι`, returns the
  class of functions `Π i, α i` sending each `i` to an element of the class `f i`.
* `Quotient.finChoiceEquiv`: A finite family of quotients is equivalent to a quotient of
  finite families.
* `Quotient.finLiftOn`: Given a fintype `ι`. A function on `Π i, α i` which respects
  setoid `S i` for each `i` can be lifted to a function on `Π i, Quotient (S i)`.
* `Quotient.finRecOn`: Recursion principle for quotients indexed by a finite type. It is the
  dependent version of `Quotient.finLiftOn`.

-/

set_option linter.unusedDecidableInType false

namespace Quotient

section List

variable {ι : Type*} [DecidableEq ι] {α : ι → Sort*} {S : ∀ i, Setoid (α i)} {β : Sort*}

def listChoice {l : List ι} (q : ∀ i ∈ l, Quotient (S i)) : @Quotient (∀ i ∈ l, α i) piSetoid :=
  match l with
  | [] => ⟦nofun⟧
  | i :: _ => Quotient.liftOn₂ (List.Pi.head (i := i) q)
    (listChoice (List.Pi.tail q))
    (⟦List.Pi.cons _ _ · ·⟧)
    (fun _ _ _ _ ha hl ↦ Quotient.sound (List.Pi.forall_rel_cons_ext ha hl))

theorem listChoice_mk {l : List ι} (a : ∀ i ∈ l, α i) : listChoice (S := S) (⟦a · ·⟧) = ⟦a⟧ :=
  match l with
  | [] => Quotient.sound nofun
  | i :: l => by
    unfold listChoice List.Pi.tail
    rw [listChoice_mk]
    exact congrArg (⟦·⟧) (List.Pi.cons_eta a)
