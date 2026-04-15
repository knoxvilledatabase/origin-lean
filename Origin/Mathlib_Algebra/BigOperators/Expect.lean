/-
Extracted from Algebra/BigOperators/Expect.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Average over a finset

This file defines `Finset.expect`, the average (aka expectation) of a function over a finset.

## Notation

* `𝔼 i ∈ s, f i` is notation for `Finset.expect s f`. It is the expectation of `f i` where `i`
  ranges over the finite set `s` (either a `Finset` or a `Set` with a `Fintype` instance).
* `𝔼 i, f i` is notation for `Finset.expect Finset.univ f`. It is the expectation of `f i` where `i`
  ranges over the finite domain of `f`.
* `𝔼 i ∈ s with p i, f i` is notation for `Finset.expect (Finset.filter p s) f`. This is referred to
  as `expectWith` in lemma names.
* `𝔼 (i ∈ s) (j ∈ t), f i j` is notation for `Finset.expect (s ×ˢ t) (fun ⟨i, j⟩ ↦ f i j)`.

## Implementation notes

This definition is a special case of the general convex combination operator in a convex space.
However:
1. We don't yet have general convex spaces.
2. The uniform weights case is an overwhelmingly useful special case which should have its own API.

When convex spaces are finally defined, we should redefine `Finset.expect` in terms of that convex
combination operator.

## TODO

* Connect `Finset.expect` with the expectation over `s` in the probability theory sense.
* Give a formulation of Jensen's inequality in this language.
-/

open Finset Function

open Fintype (card)

open scoped Pointwise

variable {ι κ M N : Type*}

local notation a " /ℚ " q => (q : ℚ≥0)⁻¹ • a

def Finset.expect [AddCommMonoid M] [Module ℚ≥0 M] (s : Finset ι) (f : ι → M) : M :=
  (#s : ℚ≥0)⁻¹ • ∑ i ∈ s, f i

namespace BigOperators

open Batteries.ExtendedBinder Lean Meta

scoped syntax (name := bigexpect) "𝔼 " bigOpBinders ("with " term)? ", " term:67 : term

scoped macro_rules (kind := bigexpect)

  | `(𝔼 $bs:bigOpBinders $[with $p?]?, $v) => do

    let processed ← processBigOpBinders bs

    let i ← bigOpBindersPattern processed

    let s ← bigOpBindersProd processed

    match p? with

    | some p => `(Finset.expect (Finset.filter (fun $i ↦ $p) $s) (fun $i ↦ $v))

    | none => `(Finset.expect $s (fun $i ↦ $v))

open Lean Meta Parser.Term PrettyPrinter.Delaborator SubExpr

open Batteries.ExtendedBinder
