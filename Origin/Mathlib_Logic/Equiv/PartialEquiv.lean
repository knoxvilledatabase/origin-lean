/-
Extracted from Logic/Equiv/PartialEquiv.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Partial equivalences

This file defines equivalences between subsets of given types.
An element `e` of `PartialEquiv α β` is made of two maps `e.toFun` and `e.invFun` respectively
from α to β and from β to α (just like equivs), which are inverse to each other on the subsets
`e.source` and `e.target` of respectively α and β.

They are designed in particular to define charts on manifolds.

The main functionality is `e.trans f`, which composes the two partial equivalences by restricting
the source and target to the maximal set where the composition makes sense.

As for equivs, we register a coercion to functions and use it in our simp normal form: we write
`e x` and `e.symm y` instead of `e.toFun x` and `e.invFun y`.

## Main definitions

* `Equiv.toPartialEquiv`: associating a partial equiv to an equiv, with source = target = univ
* `PartialEquiv.symm`: the inverse of a partial equivalence
* `PartialEquiv.trans`: the composition of two partial equivalences
* `PartialEquiv.refl`: the identity partial equivalence
* `PartialEquiv.ofSet`: the identity on a set `s`
* `EqOnSource`: equivalence relation describing the "right" notion of equality for partial
  equivalences (see below in implementation notes)

## Implementation notes

There are at least three possible implementations of partial equivalences:
* equivs on subtypes
* pairs of functions taking values in `Option α` and `Option β`, equal to none where the partial
  equivalence is not defined
* pairs of functions defined everywhere, keeping the source and target as additional data

Each of these implementations has pros and cons.
* When dealing with subtypes, one still need to define additional API for composition and
  restriction of domains. Checking that one always belongs to the right subtype makes things very
  tedious, and leads quickly to DTT hell (as the subtype `u ∩ v` is not the "same" as `v ∩ u`, for
  instance).
* With option-valued functions, the composition is very neat (it is just the usual composition, and
  the domain is restricted automatically). These are implemented in `PEquiv.lean`. For manifolds,
  where one wants to discuss thoroughly the smoothness of the maps, this creates however a lot of
  overhead as one would need to extend all classes of smoothness to option-valued maps.
* The `PartialEquiv` version as explained above is easier to use for manifolds. The drawback is that
  there is extra useless data (the values of `toFun` and `invFun` outside of `source` and `target`).
  In particular, the equality notion between partial equivs is not "the right one", i.e., coinciding
  source and target and equality there. Moreover, there are no partial equivs in this sense between
  an empty type and a nonempty type. Since empty types are not that useful, and since one almost
  never needs to talk about equal partial equivs, this is not an issue in practice.
  Still, we introduce an equivalence relation `EqOnSource` that captures this right notion of
  equality, and show that many properties are invariant under this equivalence relation.

### Local coding conventions

If a lemma deals with the intersection of a set with either source or target of a `PartialEquiv`,
then it should use `e.source ∩ s` or `e.target ∩ t`, not `s ∩ e.source` or `t ∩ e.target`.

-/

open Lean Meta Elab Tactic

/-! Implementation of the `mfld_set_tac` tactic for working with the domains of partially-defined
functions (`PartialEquiv`, `OpenPartialHomeomorph`, etc).

This is in a separate file from `Mathlib/Tactic/Attr/Register.lean` because attributes need a
new file to become functional.
-/

namespace Tactic.MfldSetTac

elab (name := mfldSetTac) "mfld_set_tac" : tactic => withMainContext do

  let g ← getMainGoal

  let goalTy := (← instantiateMVars (← g.getDecl).type).getAppFnArgs

  match goalTy with

  | (``Eq, #[_ty, _e₁, _e₂]) =>

    evalTactic (← `(tactic| (

      apply Set.ext; intro my_y

      constructor <;>

        · intro h_my_y

          try simp only [*, mfld_simps] at h_my_y

          try simp only [*, mfld_simps])))

  | (``Subset, #[_ty, _inst, _e₁, _e₂]) =>

    evalTactic (← `(tactic| (

      intro my_y h_my_y

      try simp only [*, mfld_simps] at h_my_y

      try simp only [*, mfld_simps])))

  | _ => throwError "goal should be an equality or an inclusion"

attribute [mfld_simps] and_true eq_self_iff_true Function.comp_apply

end Tactic.MfldSetTac

open Function Set

variable {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}

structure PartialEquiv (α : Type*) (β : Type*) where
  /-- The global function which has a partial inverse. Its value outside of the `source` subset is
  irrelevant. -/
  toFun : α → β
  /-- The partial inverse to `toFun`. Its value outside of the `target` subset is irrelevant. -/
  invFun : β → α
  /-- The domain of the partial equivalence. -/
  source : Set α
  /-- The codomain of the partial equivalence. -/
  target : Set β
  /-- The proposition that elements of `source` are mapped to elements of `target`. -/
  map_source' : ∀ ⦃x⦄, x ∈ source → toFun x ∈ target
  /-- The proposition that elements of `target` are mapped to elements of `source`. -/
  map_target' : ∀ ⦃x⦄, x ∈ target → invFun x ∈ source
  /-- The proposition that `invFun` is a left-inverse of `toFun` on `source`. -/
  left_inv' : ∀ ⦃x⦄, x ∈ source → invFun (toFun x) = x
  /-- The proposition that `invFun` is a right-inverse of `toFun` on `target`. -/
  right_inv' : ∀ ⦃x⦄, x ∈ target → toFun (invFun x) = x

attribute [coe] PartialEquiv.toFun

namespace PartialEquiv

variable (e : PartialEquiv α β) (e' : PartialEquiv β γ)

-- INSTANCE (free from Core): [Inhabited
