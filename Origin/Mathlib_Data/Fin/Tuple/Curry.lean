/-
Extracted from Data/Fin/Tuple/Curry.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Currying and uncurrying of n-ary functions

A function of `n` arguments can either be written as `f a₁ a₂ ⋯ aₙ` or `f' ![a₁, a₂, ⋯, aₙ]`.
This file provides the currying and uncurrying operations that convert between the two, as
n-ary generalizations of the binary `curry` and `uncurry`.

## Main definitions

* `Function.OfArity.uncurry`: convert an `n`-ary function to a function from `Fin n → α`.
* `Function.OfArity.curry`: convert a function from `Fin n → α` to an `n`-ary function.
* `Function.FromTypes.uncurry`: convert an `p`-ary heterogeneous function to a
  function from `(i : Fin n) → p i`.
* `Function.FromTypes.curry`: convert a function from `(i : Fin n) → p i` to a
  `p`-ary heterogeneous function.

-/

universe u v w w'

namespace Function.FromTypes

open Matrix (vecCons vecHead vecTail vecEmpty)

set_option linter.style.whitespace false in -- manual alignment is not recognised

def uncurry : {n : ℕ} → {p : Fin n → Type u} → {τ : Type u} →
    (f : Function.FromTypes p τ) → ((i : Fin n) → p i) → τ
  | 0    , _, _, f => fun _    => f
  | _ + 1, _, _, f => fun args => (f (args 0)).uncurry (args ∘' Fin.succ)

set_option linter.style.whitespace false in -- manual alignment is not recognised

def curry : {n : ℕ} → {p : Fin n → Type u} → {τ : Type u} →
    (((i : Fin n) → p i) → τ) → Function.FromTypes p τ
  | 0    , _, _, f => f isEmptyElim
  | _ + 1, _, _, f => fun a => curry (fun args => f (Fin.cons a args))
