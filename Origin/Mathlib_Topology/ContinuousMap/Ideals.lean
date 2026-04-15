/-
Extracted from Topology/ContinuousMap/Ideals.lean
Genuine: 6 of 8 | Dissolved: 2 | Infrastructure: 0
-/
import Origin.Core

/-!
# Ideals of continuous functions

For a topological semiring `R` and a topological space `X` there is a Galois connection between
`Ideal C(X, R)` and `Set X` given by sending each `I : Ideal C(X, R)` to
`{x : X | ∀ f ∈ I, f x = 0}ᶜ` and mapping `s : Set X` to the ideal with carrier
`{f : C(X, R) | ∀ x ∈ sᶜ, f x = 0}`, and we call these maps `ContinuousMap.setOfIdeal` and
`ContinuousMap.idealOfSet`. As long as `R` is Hausdorff, `ContinuousMap.setOfIdeal I` is open,
and if, in addition, `X` is locally compact, then `ContinuousMap.setOfIdeal s` is closed.

When `R = 𝕜` with `RCLike 𝕜` and `X` is compact Hausdorff, then this Galois connection can be
improved to a true Galois correspondence (i.e., order isomorphism) between the type `opens X` and
the subtype of closed ideals of `C(X, 𝕜)`. Because we do not have a bundled type of closed ideals,
we simply register this as a Galois insertion between `Ideal C(X, 𝕜)` and `opens X`, which is
`ContinuousMap.idealOpensGI`. Consequently, the maximal ideals of `C(X, 𝕜)` are precisely those
ideals corresponding to (complements of) singletons in `X`.

In addition, when `X` is locally compact and `𝕜` is a nontrivial topological integral domain, then
there is a natural continuous map from `X` to `WeakDual.characterSpace 𝕜 C(X, 𝕜)` given by point
evaluation, which is herein called `WeakDual.CharacterSpace.continuousMapEval`. Again, when `X` is
compact Hausdorff and `RCLike 𝕜`, more can be obtained. In particular, in that context this map is
bijective, and since the domain is compact and the codomain is Hausdorff, it is a homeomorphism,
herein called `WeakDual.CharacterSpace.homeoEval`.

## Main definitions

* `ContinuousMap.idealOfSet`: ideal of functions which vanish on the complement of a set.
* `ContinuousMap.setOfIdeal`: complement of the set on which all functions in the ideal vanish.
* `ContinuousMap.opensOfIdeal`: `ContinuousMap.setOfIdeal` as a term of `opens X`.
* `ContinuousMap.idealOpensGI`: The Galois insertion `ContinuousMap.opensOfIdeal` and
  `fun s ↦ ContinuousMap.idealOfSet ↑s`.
* `WeakDual.CharacterSpace.continuousMapEval`: the natural continuous map from a locally compact
  topological space `X` to the `WeakDual.characterSpace 𝕜 C(X, 𝕜)` which sends `x : X` to point
  evaluation at `x`, with modest hypothesis on `𝕜`.
* `WeakDual.CharacterSpace.homeoEval`: this is `WeakDual.CharacterSpace.continuousMapEval`
  upgraded to a homeomorphism when `X` is compact Hausdorff and `RCLike 𝕜`.

## Main statements

* `ContinuousMap.idealOfSet_ofIdeal_eq_closure`: when `X` is compact Hausdorff and
  `RCLike 𝕜`, `idealOfSet 𝕜 (setOfIdeal I) = I.closure` for any ideal `I : Ideal C(X, 𝕜)`.
* `ContinuousMap.setOfIdeal_ofSet_eq_interior`: when `X` is compact Hausdorff and `RCLike 𝕜`,
  `setOfIdeal (idealOfSet 𝕜 s) = interior s` for any `s : Set X`.
* `ContinuousMap.ideal_isMaximal_iff`: when `X` is compact Hausdorff and `RCLike 𝕜`, a closed
  ideal of `C(X, 𝕜)` is maximal if and only if it is `idealOfSet 𝕜 {x}ᶜ` for some `x : X`.

## Implementation details

Because there does not currently exist a bundled type of closed ideals, we don't provide the actual
order isomorphism described above, and instead we only consider the Galois insertion
`ContinuousMap.idealOpensGI`.

## Tags

ideal, continuous function, compact, Hausdorff
-/

open scoped NNReal

namespace ContinuousMap

open TopologicalSpace

section IsTopologicalRing

variable {X R : Type*} [TopologicalSpace X] [Semiring R]

variable [TopologicalSpace R] [IsTopologicalSemiring R]

variable (R)

def idealOfSet (s : Set X) : Ideal C(X, R) where
  carrier := {f : C(X, R) | ∀ x ∈ sᶜ, f x = 0}
  add_mem' {f g} hf hg x hx := by simp [hf x hx, hg x hx, add_zero]
  zero_mem' _ _ := rfl
  smul_mem' c _ hf x hx := mul_zero (c x) ▸ congr_arg (fun y => c x * y) (hf x hx)

theorem idealOfSet_closed [T2Space R] (s : Set X) :
    IsClosed (idealOfSet R s : Set C(X, R)) := by
  simp only [idealOfSet, Submodule.coe_set_mk, Set.setOf_forall]
  exact isClosed_iInter fun x => isClosed_iInter fun _ =>
    isClosed_eq (continuous_eval_const x) continuous_const

variable {R}

theorem mem_idealOfSet {s : Set X} {f : C(X, R)} :
    f ∈ idealOfSet R s ↔ ∀ ⦃x : X⦄, x ∈ sᶜ → f x = 0 := by
  convert Iff.rfl

-- DISSOLVED: notMem_idealOfSet

def setOfIdeal (I : Ideal C(X, R)) : Set X :=
  {x : X | ∀ f ∈ I, (f : C(X, R)) x = 0}ᶜ

theorem notMem_setOfIdeal {I : Ideal C(X, R)} {x : X} :
    x ∉ setOfIdeal I ↔ ∀ ⦃f : C(X, R)⦄, f ∈ I → f x = 0 := by
  rw [← Set.mem_compl_iff, setOfIdeal, compl_compl, Set.mem_setOf]

-- DISSOLVED: mem_setOfIdeal

theorem setOfIdeal_open [T2Space R] (I : Ideal C(X, R)) : IsOpen (setOfIdeal I) := by
  simp only [setOfIdeal, Set.setOf_forall, isOpen_compl_iff]
  exact
    isClosed_iInter fun f =>
      isClosed_iInter fun _ => isClosed_eq (map_continuous f) continuous_const
