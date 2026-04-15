/-
Extracted from LinearAlgebra/Multilinear/Basic.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Multilinear maps

We define multilinear maps as maps from `∀ (i : ι), M₁ i` to `M₂` which are linear in each
coordinate. Here, `M₁ i` and `M₂` are modules over a ring `R`, and `ι` is an arbitrary type
(although some statements will require it to be a fintype). This space, denoted by
`MultilinearMap R M₁ M₂`, inherits a module structure by pointwise addition and multiplication.

## Main definitions

* `MultilinearMap R M₁ M₂` is the space of multilinear maps from `∀ (i : ι), M₁ i` to `M₂`.
* `f.map_update_smul` is the multiplicativity of the multilinear map `f` along each coordinate.
* `f.map_update_add` is the additivity of the multilinear map `f` along each coordinate.
* `f.map_smul_univ` expresses the multiplicativity of `f` over all coordinates at the same time,
  writing `f (fun i => c i • m i)` as `(∏ i, c i) • f m`.
* `f.map_add_univ` expresses the additivity of `f` over all coordinates at the same time, writing

  `f (m + m')` as the sum over all subsets `s` of `ι` of `f (s.piecewise m m')`.
* `f.map_sum` expresses `f (Σ_{j₁} g₁ j₁, ..., Σ_{jₙ} gₙ jₙ)` as the sum of
  `f (g₁ (r 1), ..., gₙ (r n))` where `r` ranges over all possible functions.

See `Mathlib/LinearAlgebra/Multilinear/Curry.lean` for the currying of multilinear maps.

## Implementation notes

Expressing that a map is linear along the `i`-th coordinate when all other coordinates are fixed
can be done in two (equivalent) different ways:

* fixing a vector `m : ∀ (j : ι - i), M₁ j.val`, and then choosing separately the `i`-th coordinate
* fixing a vector `m : ∀ j, M₁ j`, and then modifying its `i`-th coordinate

The second way is more artificial as the value of `m` at `i` is not relevant, but it has the
advantage of avoiding subtype inclusion issues. This is the definition we use, based on
`Function.update` that allows to change the value of `m` at `i`.

Note that the use of `Function.update` requires a `DecidableEq ι` term to appear somewhere in the
statement of `MultilinearMap.map_update_add'` and `MultilinearMap.map_update_smul'`.
Three possible choices are:

1. Requiring `DecidableEq ι` as an argument to `MultilinearMap` (as we did originally).
2. Using `Classical.decEq ι` in the statement of `map_add'` and `map_smul'`.
3. Quantifying over all possible `DecidableEq ι` instances in the statement of `map_add'` and
   `map_smul'`.

Option 1 works fine, but puts unnecessary constraints on the user
(the zero map certainly does not need decidability).
Option 2 looks great at first, but in the common case when `ι = Fin n`
it introduces non-defeq decidability instance diamonds
within the context of proving `map_update_add'` and `map_update_smul'`,
of the form `Fin.decidableEq n = Classical.decEq (Fin n)`.
Option 3 of course does something similar, but of the form `Fin.decidableEq n = _inst`,
which is much easier to clean up since `_inst` is a free variable
and so the equality can just be substituted.
-/

open Fin Function Finset Set

universe uR uS uι v v' v₁ v₁' v₁'' v₂ v₃ v₄

variable {R : Type uR} {S : Type uS} {ι : Type uι} {n : ℕ}
  {M : Fin n.succ → Type v} {M₁ : ι → Type v₁} {M₁' : ι → Type v₁'} {M₁'' : ι → Type v₁''}

variable {M₂ : Type v₂} {M₃ : Type v₃} {M₄ : Type v₄} {M' : Type v'}

set_option genInjectivity false in

structure MultilinearMap (R : Type uR) {ι : Type uι} (M₁ : ι → Type v₁) (M₂ : Type v₂) [Semiring R]
  [∀ i, AddCommMonoid (M₁ i)] [AddCommMonoid M₂] [∀ i, Module R (M₁ i)] [Module R M₂] where
  /-- The underlying multivariate function of a multilinear map. -/
  toFun : (∀ i, M₁ i) → M₂
  /-- A multilinear map is additive in every argument. -/
  map_update_add' :
    ∀ [DecidableEq ι] (m : ∀ i, M₁ i) (i : ι) (x y : M₁ i),
      toFun (update m i (x + y)) = toFun (update m i x) + toFun (update m i y)
  /-- A multilinear map is compatible with scalar multiplication in every argument. -/
  map_update_smul' :
    ∀ [DecidableEq ι] (m : ∀ i, M₁ i) (i : ι) (c : R) (x : M₁ i),
      toFun (update m i (c • x)) = c • toFun (update m i x)

namespace MultilinearMap

section Semiring

variable [Semiring R] [∀ i, AddCommMonoid (M i)] [∀ i, AddCommMonoid (M₁ i)] [AddCommMonoid M₂]
  [AddCommMonoid M₃] [AddCommMonoid M'] [∀ i, Module R (M i)] [∀ i, Module R (M₁ i)] [Module R M₂]
  [Module R M₃] [Module R M'] (f f' : MultilinearMap R M₁ M₂)

-- INSTANCE (free from Core): :

initialize_simps_projections MultilinearMap (toFun → apply)
