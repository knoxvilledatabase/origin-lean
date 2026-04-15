/-
Extracted from GroupTheory/Coxeter/Length.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The length function, reduced words, and descents

Throughout this file, `B` is a type and `M : CoxeterMatrix B` is a Coxeter matrix.
`cs : CoxeterSystem M W` is a Coxeter system; that is, `W` is a group, and `cs` holds the data
of a group isomorphism `W ≃* M.group`, where `M.group` refers to the quotient of the free group on
`B` by the Coxeter relations given by the matrix `M`. See `Mathlib/GroupTheory/Coxeter/Basic.lean`
for more details.

Given any element $w \in W$, its *length* (`CoxeterSystem.length`), denoted $\ell(w)$, is the
minimum number $\ell$ such that $w$ can be written as a product of a sequence of $\ell$ simple
reflections:
$$w = s_{i_1} \cdots s_{i_\ell}.$$
We prove for all $w_1, w_2 \in W$ that $\ell (w_1 w_2) \leq \ell (w_1) + \ell (w_2)$
and that $\ell (w_1 w_2)$ has the same parity as $\ell (w_1) + \ell (w_2)$.

We define a *reduced word* (`CoxeterSystem.IsReduced`) for an element $w \in W$ to be a way of
writing $w$ as a product of exactly $\ell(w)$ simple reflections. Every element of $W$ has a reduced
word.

We say that $i \in B$ is a *left descent* (`CoxeterSystem.IsLeftDescent`) of $w \in W$ if
$\ell(s_i w) < \ell(w)$. We show that if $i$ is a left descent of $w$, then
$\ell(s_i w) + 1 = \ell(w)$. On the other hand, if $i$ is not a left descent of $w$, then
$\ell(s_i w) = \ell(w) + 1$. We similarly define right descents (`CoxeterSystem.IsRightDescent`) and
prove analogous results.

## Main definitions

* `cs.length`
* `cs.IsReduced`
* `cs.IsLeftDescent`
* `cs.IsRightDescent`

## References

* [A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*](bjorner2005)

-/

assert_not_exists TwoSidedIdeal

namespace CoxeterSystem

open List Matrix Function

variable {B W : Type*} [Group W]

variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

local prefix:100 "s " => cs.simple

local prefix:100 "π " => cs.wordProd

/-! ### Length -/

private theorem exists_word_with_prod (w : W) : ∃ n ω, n = ω.length ∧ π ω = w := by
  rcases cs.wordProd_surjective w with ⟨ω, rfl⟩
  use ω.length, ω

open scoped Classical in
