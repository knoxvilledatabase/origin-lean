# For AI Agents

**Read this first. Then build.**

---

## What This Project Is

A standalone Lean 4 library that restates mathematics through three constructors (origin, container, contents) instead of Mathlib's 17 zero-management typeclasses. Zero Mathlib dependency. Builds in under 1 second.

The question: how many lines of code does it take to do the same math as Mathlib's 2,160,000 lines?

Current answer: 10,615 lines cover 19 domains with deep dives. Predicted full answer: ~23,000 lines.

## Where We Are

**79 files. 10,615 lines. 19 domains. All build clean.**

```bash
cd origin-lean
lake build    # <1 second
```

## How to Understand the Codebase

Read in this order:

1. **[Val/Foundation.lean](Val/Foundation.lean)** (217 lines) — the app. Three constructors, four rules, 44 simp lemmas. Everything starts here. Read the whole file.

2. **[Val/Algebra.lean](Val/Algebra.lean)** (198 lines) — lifted ring laws. The pattern: `cases <;> simp <;> apply h`. Every domain calls this. Read the whole file.

3. **[Val/Category/Preadditive.lean](Val/Category/Preadditive.lean)** (~109 lines) — the proof the architecture works. Every theorem is a one-liner calling Algebra. This is what domain files look like.

4. **[README.md](README.md)** — the big picture, the numbers, the tree.

## What Is Next

**Read [PROGRESSION_STEP3.md](PROGRESSION_STEP3.md).** That is the current work.

Steps 1 and 2 are complete (history only):
- [PROGRESSION.md](PROGRESSION.md) — how we got here (the full circle from standalone to Mathlib and back). Read for context and lessons learned. Do not re-do this work.
- [PROGRESSION_STEP2.md](PROGRESSION_STEP2.md) — deep dives, completed. Read for reference on what was done. Do not re-do this work.

Step 3 is the active work: restate all of Mathlib's 88,494 theorems. 13 stairs. Start with Data/Nat/.

## The Architecture

### Val α is a Django abstract base model

Foundation.lean is the app. Every domain is a model. The foundation defines the dispatch and the lifted laws. Domain files import the foundation and write domain-specific definitions.

### Explicit function parameters, not typeclasses

```lean
-- YES: explicit parameter
def mul (f : α → α → α) : Val α → Val α → Val α

-- NO: typeclass
def mul [Mul α] : Val α → Val α → Val α
```

This is a deliberate choice. Typeclasses cause diamond inheritance at the arithmetic level. Explicit parameters avoid it entirely. Zero Mathlib. Zero diamonds. Zero infrastructure.

### The proof pattern

Every lifted law follows:

```lean
theorem right_distrib (mulF addF : α → α → α)
    (h : ∀ a b c, mulF (addF a b) c = addF (mulF a c) (mulF b c))
    (a b c : Val α) : mul mulF (add addF a b) c = add addF (mul mulF a c) (mul mulF b c) := by
  cases a <;> cases b <;> cases c <;> simp <;> apply h
```

Origin cases: `simp` closes them (Foundation's 44 simp lemmas).
Non-origin cases: `simp` reduces to `constructor(expr)`, then `apply h` uses α's law.

If this pattern doesn't work, Foundation is missing a simp lemma. Step down. Add the lemma. Step back up.

### The stair rule

If a proof is fighting, the property belongs one level lower. Always strengthen the base first. The domain proof should then be trivial.

### The file structure

```
Val/
  Foundation.lean           — the app. simp set. dispatch. sort predicates.
  Algebra.lean              — lifted ring laws. every domain calls this.
  RingField.lean            — inverse, division, dissolved hypotheses.
  OrderedField.lean         — ordering within contents.
  VectorSpace.lean          — scalar multiplication, module laws.
  PolyRing.lean             — polynomial evaluation, Horner.
  FunctionalAnalysis.lean   — norms, operators.
  SpectralTheory.lean       — spectrum, resolvent.
  Probability.lean          — random variables, expectation.
  AlgebraicGeometry.lean    — Spec, Zariski, schemes.
  DifferentialGeometry.lean — tangent vectors, forms, connections.
  HomologicalAlgebra.lean   — chain complexes, exact sequences.
  Analysis/        (23 files) — limits through asymptotic analysis
  Topology/         (9 files) — compactification through sheaves
  Category/        (10 files) — functors through preadditive
  LinearAlgebra/    (7 files) — determinants through projective modules
  MeasureTheory/    (7 files) — measures through specific constructions
  RingTheory/      (11 files) — ideals through schemes
```

## Key Lessons (Do Not Repeat These Mistakes)

### Don't try to import Mathlib's typeclasses

We tried creating a Prelude.lean that defined Semigroup, Monoid, Ring from scratch. Diamond inheritance at the arithmetic level. Mathlib solves this with thousands of lines of infrastructure. We don't re-solve it. We use explicit function parameters instead.

### Don't skip the base

We tried writing CategoryPreadditive before strengthening Foundation with simp lemmas. Every proof fought. 27-case splits. Then we built the simp set and lifted laws. CategoryPreadditive became one-liners. Always build the base first.

### The typeclass ceiling is correct

Val α is NOT a Semiring, Ring, or AddGroup. `contents(0) * origin = origin`, not `contents(0)`. The ground absorbs. Don't try to register Ring on Val α. The ring lives inside contents. The sort lives outside.

### Extend, never duplicate

If you see the same `cases <;> simp` pattern in multiple files, the property belongs in Foundation or Algebra. Move it down. Prove it once. Call it everywhere.

## How to Add a Domain File

```lean
import Val.Algebra

namespace Val

universe u
variable {α : Type u}

-- Define domain-specific concepts using explicit parameters
def myOp (f : α → α → α) (x y : Val α) : Val α := mul f x y

-- Prove domain-specific theorems calling the base
theorem myOp_contents (f : α → α → α) (a b : α) :
    myOp f (contents a) (contents b) = contents (f a b) := by simp [myOp]

theorem myOp_origin (f : α → α → α) (x : Val α) :
    myOp f origin x = origin := by simp [myOp]

end Val
```

If the proof takes more than one line, the base is missing something. Step down.

## How to Restate a Mathlib Theorem

1. Find the Mathlib theorem
2. Identify the `≠ 0` hypotheses, typeclasses from the 17, zero-management
3. Translate: `[Ring α]` becomes explicit `(mulF addF : α → α → α)` etc.
4. Prove: should be `by simp` or a one-liner calling Algebra
5. If not, the base needs a new simp lemma or lifted law

## Build and Verify

```bash
lake build    # builds all 79 files in <1 second
```

Zero sorries. Zero Mathlib. Zero typeclasses. Builds in seconds.

The kill switch: if something becomes more complex than the explicit parameter approach, we missed something at the foundation level. Step down.
