# For AI Agents

**Read this first. Then build.**

---

## What This Project Is

A standalone Lean 4 library that restates mathematics through three constructors (origin, container, contents) instead of Mathlib's 17 zero-management typeclasses. Zero Mathlib dependency. Builds in under 1 second.

The question: how many lines of code does it take to do the same math as Mathlib's 2,160,000 lines?

Current answer: **10,885 lines. 11 files. 32 domains. 99.5% reduction.**

## Where We Are

**11 files. 10,885 lines. 32 domains. All build clean.**

```bash
cd origin-lean
lake build    # <1 second
```

## How to Understand the Codebase

Read in this order:

1. **[Val/Foundation.lean](Val/Foundation.lean)** (268 lines) — the app. Three constructors, four rules, `valMap`, `valPair`, simp lemmas. Everything starts here. Read the whole file.

2. **[Val/Algebra.lean](Val/Algebra.lean)** (1,433 lines) — lifted ring laws + 6 domain sections (ring/field, ordered field, vector spaces, polynomial ring, functional analysis, spectral theory, representation theory, field theory, group theory). The pattern: `cases <;> simp <;> apply h`. Every domain calls this.

3. **Any domain file** — pick one. Every section is the same pattern: `abbrev`, `by simp`, one-liner calling the base. 2 reads (Foundation + domain file) gives full context.

4. **[README.md](README.md)** — the big picture, the numbers, the tree.

## How We Got Here

5. **[PROGRESSION.md](PROGRESSION.md)** (COMPLETE, history only) — the full circle from standalone to Mathlib and back. Why explicit parameters, why not typeclasses, why the Django model, why the stair rule.

6. **[PROGRESSION_STEP2.md](PROGRESSION_STEP2.md)** (COMPLETE, history only) — how 19 files became 79 files. Deep dives, domain folder structure.

7. **[PROGRESSION_STEP3.md](PROGRESSION_STEP3.md)** (STRUCTURALLY COMPLETE) — how 79 files became 11 files covering all 32 domains. Deduplication, consolidation, stair execution. Structure built and compiling, but not exhaustively verified against Mathlib's theorem list.

8. **[PROGRESSION_STEP4.md](PROGRESSION_STEP4.md)** (COMPLETE) — exhaustive theorem mapping of all 173,646 Mathlib theorems. 67.3% are infrastructure Val absorbs. 32.7% (56,815) are genuinely new mathematics.

## What Is Next

9. **[PROGRESSION_STEP5.md](PROGRESSION_STEP5.md)** — the active work. Write the 56,815 genuinely new theorems on the Val foundation. Priority: Analysis + Algebra + Data first (AI inference impact). Target: ~150,000 lines total, 93% reduction from Mathlib. The training corpus that proves AI can learn math with less energy.

## The Architecture

### Val α is a Django abstract base model

Foundation.lean is the app. Every domain is a section. The foundation defines the dispatch and the lifted laws. Domain files import the foundation and extend with domain-specific definitions.

### Three core operations handle everything

```lean
-- Unary sort-preserving map (covers norm, abs, trace, homomorphism, Galois action, ...)
def valMap (f : α → β) : Val α → Val β

-- Binary same-type (covers inner product, bilinear, group multiplication, flow, ...)
def mul (f : α → α → α) : Val α → Val α → Val α

-- Binary cross-type (covers tensor product)
def valPair : Val α → Val β → Val (α × β)
```

Domain definitions are `abbrev` aliases: `abbrev norm := valMap normF`. One line. The base's simp lemmas fire through the alias automatically.

### Explicit function parameters, not typeclasses

```lean
-- YES: explicit parameter
def mul (f : α → α → α) : Val α → Val α → Val α

-- NO: typeclass
def mul [Mul α] : Val α → Val α → Val α
```

Typeclasses cause diamond inheritance at the arithmetic level. Explicit parameters avoid it entirely. Zero Mathlib. Zero diamonds. Zero infrastructure.

### The proof pattern

Every lifted law follows:

```lean
theorem right_distrib (mulF addF : α → α → α)
    (h : ∀ a b c, mulF (addF a b) c = addF (mulF a c) (mulF b c))
    (a b c : Val α) : mul mulF (add addF a b) c = add addF (mul mulF a c) (mul mulF b c) := by
  cases a <;> cases b <;> cases c <;> simp <;> apply h
```

Origin cases: `simp` closes them (Foundation's simp lemmas).
Non-origin cases: `simp` reduces to `constructor(expr)`, then `apply h` uses α's law.

If this pattern doesn't work, Foundation is missing a simp lemma. Step down. Add the lemma. Step back up.

### The stair rule

If a proof is fighting, the property belongs one level lower. Always strengthen the base first. The domain proof should then be trivial.

### The file structure

```
Val/
  Foundation.lean      268  — the type, ops, simp set
  Algebra.lean       1,433  — lifted laws + ring/field + ordered + vector + poly
                              + functional + spectral + representation + field + group theory
  Category.lean      1,353  — functors, monoidal, limits, preadditive, abelian, linear
                              + enriched + condensed + model theory
  RingTheory.lean    1,555  — ideals, localization, Noetherian, Dedekind, graded, tensor
                              + schemes + number theory
  LinearAlgebra.lean   504  — determinants, bilinear, modules, finite dim, matrices, projective
  Analysis.lean      2,302  — limits through asymptotic analysis (23 domains)
  MeasureTheory.lean   469  — measures, integrals, decomposition
  Topology.lean        978  — compactification through sheaves + dynamics
  Applied.lean       1,108  — probability, homological algebra, information theory,
                              set theory, computability, logic, combinatorics
  Geometry.lean        210  — algebraic + differential geometry
  Data.lean            705  — nat, int, rat, list, set, finset, multiset
```

## Key Lessons (Do Not Repeat These Mistakes)

### Don't try to import Mathlib's typeclasses

We tried creating a Prelude.lean that defined Semigroup, Monoid, Ring from scratch. Diamond inheritance at the arithmetic level. Mathlib solves this with thousands of lines of infrastructure. We don't re-solve it. We use explicit function parameters instead.

### Don't skip the base

We tried writing CategoryPreadditive before strengthening Foundation with simp lemmas. Every proof fought. 27-case splits. Then we built the simp set and lifted laws. CategoryPreadditive became one-liners. Always build the base first.

### The typeclass ceiling is correct

Val α is NOT a Semiring, Ring, or AddGroup. `contents(0) * origin = origin`, not `contents(0)`. The ground absorbs. Don't try to register Ring on Val α. The ring lives inside contents. The sort lives outside.

### Extend, never duplicate

If you see the same pattern in multiple sections, the property belongs in Foundation or Algebra. Move it down. Prove it once. Call it everywhere. We found 18% of the codebase was duplication — 28 duplicate definitions, ~316 duplicate theorems. All eliminated.

### Strip until it hurts

Minimalist extremism: strip away everything until it hurts, then only add back what's necessary. If your solution feels robust and "properly engineered" — you haven't stripped enough. The discomfort of "too simple" is the signal you're on the right path.

## How to Add a Domain Section

```lean
-- In the appropriate domain file (Algebra.lean, Category.lean, etc.)
-- Add a section before `end Val`:

-- ============================================================================
-- My New Domain
-- ============================================================================

-- Unary sort-preserving maps: one line
abbrev myTransform (f : α → α) : Val α → Val α := valMap f

-- Domain theorem: by simp
theorem my_theorem (f : α → α → α) (a b : α) :
    mul f (contents a) (contents b) ≠ origin := by simp
```

No new files. Sections in existing files. If a proof takes more than one line, the base is missing something. Step down.

## How to Restate a Mathlib Theorem

1. Find the Mathlib theorem
2. Identify the `≠ 0` hypotheses, typeclasses from the 17, zero-management
3. Translate: `[Ring α]` becomes explicit `(mulF addF : α → α → α)` etc.
4. Check: is this just `valMap` under a domain name? → `abbrev`
5. Prove: should be `by simp` or a one-liner calling Algebra
6. If not, the base needs a new simp lemma or lifted law

## Build and Verify

```bash
lake build    # builds all 11 files in <1 second
```

Zero sorries. Zero Mathlib. Zero typeclasses. Builds in seconds.

The kill switch: if something becomes more complex than the explicit parameter approach, we missed something at the foundation level. Step down.
