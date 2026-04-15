/-
Extracted from Analysis/Calculus/IteratedDeriv/Defs.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# One-dimensional iterated derivatives

We define the `n`-th derivative of a function `f : 𝕜 → F` as a function
`iteratedDeriv n f : 𝕜 → F`, as well as a version on domains `iteratedDerivWithin n f s : 𝕜 → F`,
and prove their basic properties.

## Main definitions and results

Let `𝕜` be a nontrivially normed field, and `F` a normed vector space over `𝕜`. Let `f : 𝕜 → F`.

* `iteratedDeriv n f` is the `n`-th derivative of `f`, seen as a function from `𝕜` to `F`.
  It is defined as the `n`-th Fréchet derivative (which is a multilinear map) applied to the
  vector `(1, ..., 1)`, to take advantage of all the existing framework, but we show that it
  coincides with the naive iterative definition.
* `iteratedDeriv_eq_iterate` states that the `n`-th derivative of `f` is obtained by starting
  from `f` and differentiating it `n` times.
* `iteratedDerivWithin n f s` is the `n`-th derivative of `f` within the domain `s`. It only
  behaves well when `s` has the unique derivative property.
* `iteratedDerivWithin_eq_iterate` states that the `n`-th derivative of `f` in the domain `s` is
  obtained by starting from `f` and differentiating it `n` times within `s`. This only holds when
  `s` has the unique derivative property.

## Implementation details

The results are deduced from the corresponding results for the more general (multilinear) iterated
Fréchet derivative. For this, we write `iteratedDeriv n f` as the composition of
`iteratedFDeriv 𝕜 n f` and a continuous linear equiv. As continuous linear equivs respect
differentiability and commute with differentiation, this makes it possible to prove readily that
the derivative of the `n`-th derivative is the `n+1`-th derivative in `iteratedDerivWithin_succ`,
by translating the corresponding result `iteratedFDerivWithin_succ_apply_left` for the
iterated Fréchet derivative.
-/

noncomputable section

open scoped Topology

open Filter Asymptotics Set

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

def iteratedDeriv (n : ℕ) (f : 𝕜 → F) (x : 𝕜) : F :=
  (iteratedFDeriv 𝕜 n f x : (Fin n → 𝕜) → F) fun _ : Fin n => 1

def iteratedDerivWithin (n : ℕ) (f : 𝕜 → F) (s : Set 𝕜) (x : 𝕜) : F :=
  (iteratedFDerivWithin 𝕜 n f s x : (Fin n → 𝕜) → F) fun _ : Fin n => 1

variable {n : ℕ} {f : 𝕜 → F} {s : Set 𝕜} {x : 𝕜}
