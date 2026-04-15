/-
Extracted from NumberTheory/Dioph.lean
Genuine: 5 of 6 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Diophantine functions and Matiyasevic's theorem

Hilbert's tenth problem asked whether there exists an algorithm which for a given integer polynomial
determines whether this polynomial has integer solutions. It was answered in the negative in 1970,
the final step being completed by Matiyasevic who showed that the power function is Diophantine.

Here a function is called Diophantine if its graph is Diophantine as a set. A subset `S ⊆ ℕ ^ α` in
turn is called Diophantine if there exists an integer polynomial on `α ⊕ β` such that `v ∈ S` iff
there exists `t : ℕ^β` with `p (v, t) = 0`.

## Main definitions

* `IsPoly`: a predicate stating that a function is a multivariate integer polynomial.
* `Poly`: the type of multivariate integer polynomial functions.
* `Dioph`: a predicate stating that a set is Diophantine, i.e. a set `S ⊆ ℕ^α` is
  Diophantine if there exists a polynomial on `α ⊕ β` such that `v ∈ S` iff there
  exists `t : ℕ^β` with `p (v, t) = 0`.
* `DiophFn`: a predicate on a function stating that it is Diophantine in the sense that its graph
  is Diophantine as a set.

## Main statements

* `pell_dioph` states that solutions to Pell's equation form a Diophantine set.
* `pow_dioph` states that the power function is Diophantine, a version of Matiyasevic's theorem.

## References

* [M. Carneiro, _A Lean formalization of Matiyasevic's theorem_][carneiro2018matiyasevic]
* [M. Davis, _Hilbert's tenth problem is unsolvable_][MR317916]

## Tags

Matiyasevic's theorem, Hilbert's tenth problem

## TODO

* Finish the solution of Hilbert's tenth problem.
* Connect `Poly` to `MvPolynomial`
-/

open Fin2 Function Nat Sum

local infixr:67 " ::ₒ " => Option.elim'

local infixr:65 " ⊗ " => Sum.elim

universe u

/-!
### Multivariate integer polynomials

Note that this duplicates `MvPolynomial`.
-/

section Polynomials

variable {α β : Type*}

inductive IsPoly : ((α → ℕ) → ℤ) → Prop
  | proj : ∀ i, IsPoly fun x : α → ℕ => x i
  | const : ∀ n : ℤ, IsPoly fun _ : α → ℕ => n
  | sub : ∀ {f g : (α → ℕ) → ℤ}, IsPoly f → IsPoly g → IsPoly fun x => f x - g x
  | mul : ∀ {f g : (α → ℕ) → ℤ}, IsPoly f → IsPoly g → IsPoly fun x => f x * g x

theorem IsPoly.neg {f : (α → ℕ) → ℤ} : IsPoly f → IsPoly (-f) := by
  rw [← zero_sub]; exact (IsPoly.const 0).sub

theorem IsPoly.add {f g : (α → ℕ) → ℤ} (hf : IsPoly f) (hg : IsPoly g) : IsPoly (f + g) := by
  rw [← sub_neg_eq_add]; exact hf.sub hg.neg

def Poly (α : Type u) := { f : (α → ℕ) → ℤ // IsPoly f }

namespace Poly

-- INSTANCE (free from Core): instFunLike

protected theorem isPoly (f : Poly α) : IsPoly f := f.2
