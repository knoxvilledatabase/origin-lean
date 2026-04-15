/-
Extracted from Data/Fintype/Inv.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Computable inverses for injective/surjective functions on finite types

## Main results

* `Function.Injective.invOfMemRange`, `Embedding.invOfMemRange`, `Fintype.bijInv`:
  computable versions of `Function.invFun`.
* `Fintype.choose`: computably obtain a witness for `ExistsUnique`.
-/

assert_not_exists Monoid

open Function

open Nat

universe u v

variable {α β γ : Type*}

section Inv

namespace Function

variable [Fintype α] [DecidableEq β]

namespace Injective

variable {f : α → β} (hf : Function.Injective f)

def invOfMemRange : Set.range f → α := fun b =>
  Finset.choose (fun a => f a = b) Finset.univ
    ((existsUnique_congr (by simp)).mp (hf.existsUnique_of_mem_range b.property))

theorem left_inv_of_invOfMemRange (b : Set.range f) : f (hf.invOfMemRange b) = b :=
  (Finset.choose_spec (fun a => f a = b) _ _).right
