# Step 3: Restate Mathlib Through the Val Foundation

## The Goal

Restate Mathlib's 88,494 theorems through the Val foundation. The prediction: ~30,000 lines of code. ~28,000 theorems don't need to exist (the sort system eliminates them). ~19,000 become one-liners. ~42,000 exist with shorter proofs.

The reusability compounds at every level. The foundation does the work. The domains call the base.

## The Map

Mathlib has 2,160,000 lines across 8,200 files. Here's how it maps to origin-lean:

### Already covered (foundations + deep dives)

| Mathlib directory | Mathlib lines | origin-lean | Status |
|---|---|---|---|
| Algebra/ | 312,262 | Val/Algebra.lean + Val/RingField.lean | Foundation covered |
| Analysis/ | 235,193 | Val/Analysis/ (23 files) | Foundation + deep dives |
| CategoryTheory/ | 256,803 | Val/Category/ (10 files) | Foundation + deep dives |
| Topology/ | 182,394 | Val/Topology/ (9 files) | Foundation + deep dives |
| RingTheory/ | 175,123 | Val/RingTheory/ (11 files) | Foundation + deep dives |
| LinearAlgebra/ | 102,475 | Val/LinearAlgebra/ (7 files) | Foundation + deep dives |
| MeasureTheory/ | 113,074 | Val/MeasureTheory/ (7 files) | Foundation + deep dives |
| Order/ | 95,034 | Val/OrderedField.lean | Foundation covered |
| Probability/ | 39,827 | Val/Probability.lean | Foundation covered |
| AlgebraicGeometry/ | 45,504 | Val/AlgebraicGeometry.lean | Foundation covered |
| Geometry/ | 51,622 | Val/DifferentialGeometry.lean | Foundation covered |
| AlgebraicTopology/ | 26,493 | Val/HomologicalAlgebra.lean | Foundation covered |
| **Subtotal** | **1,634,804** | **79 files, 10,615 lines** | |

### Not yet covered

| Mathlib directory | Lines | Files | What it is |
|---|---|---|---|
| Data/ | 156,875 | 642 | Data structures, types, lists, sets, finsets |
| NumberTheory/ | 68,239 | 231 | Primes, modular arithmetic, Diophantine |
| Combinatorics/ | 53,907 | 170 | Graphs, partitions, Young tableaux |
| GroupTheory/ | 51,533 | 160 | Group actions, Sylow, solvable |
| FieldTheory/ | 26,919 | 78 | Galois theory, splitting fields |
| SetTheory/ | 19,486 | 46 | Ordinals, cardinals, ZFC |
| Computability/ | 14,993 | 34 | Turing machines, decidability |
| Logic/ | 14,362 | 57 | Propositional, first-order |
| ModelTheory/ | 12,853 | 34 | Structures, ultraproducts |
| RepresentationTheory/ | 12,211 | 37 | Group representations, characters |
| Dynamics/ | 6,514 | 31 | Ergodic theory, flows |
| Condensed/ | 4,326 | 33 | Condensed mathematics |
| InformationTheory/ | 1,457 | 6 | Entropy, mutual information |
| **Subtotal** | **443,675** | **1,559** | |

### Infrastructure (not math, not restated)

| Mathlib directory | Lines | What it is |
|---|---|---|
| Tactic/ | ~50,000 | Custom tactics (simp, ring, linarith) |
| Mathport/ | ~5,000 | Lean 3 migration |
| Deprecated/ | ~3,000 | Old code |
| Testing/ | ~1,000 | Test infrastructure |
| Util/ | ~500 | Utilities |
| Lean/ | ~2,000 | Lean extensions |
| Control/ | 4,221 | Monads, functors (Lean-level) |
| **Subtotal** | **~66,000** | **Not math. Not restated.** |

### The arithmetic

| Category | Mathlib lines | Prediction |
|---|---|---|
| Already covered domains | 1,634,804 | 10,615 (measured) |
| Uncovered domains | 443,675 | ~12,000 (estimated) |
| Infrastructure | ~66,000 | 0 (not math) |
| **Total** | **~2,160,000** | **~23,000** |

## The Stairs

Each stair is one Mathlib subdirectory. Start at the bottom of the dependency tree, work up. Each stair builds clean before moving up.

### Tier 1: Foundation domains (already done)

These are the 12 domains origin-lean already covers. 1,634,804 Mathlib lines → 10,615 origin-lean lines. Done.

### Tier 2: Data structures

**Stair 1: Val/Data/** — Mathlib/Data/ (156,875 lines, 642 files)

This is the largest uncovered directory. Most of it is type definitions and basic lemmas about lists, sets, finsets, multisets, nat, int, rat, real, complex. Much of the zero management in Data/ is about `Nat.zero`, `List.nil`, `Finset.empty` — the "nothing" variants of data structures.

With Val: `origin` is the empty structure. `contents(list)` is a list. The pattern is the same.

Start with the most-used subdirectories:
- Data/Nat/ — natural numbers
- Data/Int/ — integers  
- Data/Rat/ — rationals
- Data/List/ — lists
- Data/Set/ — sets
- Data/Finset/ — finite sets

Each becomes a file in Val/Data/. Import Foundation. Define the sort-aware versions. The `≠ 0` hypotheses on Nat.div, Int.div dissolve.

### Tier 3: Group and Field theory

**Stair 2: Val/GroupTheory.lean** — Mathlib/GroupTheory/ (51,533 lines)

Group actions, Sylow theorems, solvable groups. Most of this is pure algebra that lives within contents. The sort adds nothing to group theory except at the boundary (trivial group = origin).

**Stair 3: Val/FieldTheory/** — Mathlib/FieldTheory/ (26,919 lines)

Galois theory, splitting fields, algebraic closures. Field theory is entirely within contents. The sort matters for the minimal polynomial (degree ≠ 0 hypotheses dissolve).

### Tier 4: Number theory and combinatorics

**Stair 4: Val/NumberTheory/** — Mathlib/NumberTheory/ (68,239 lines)

Primes, modular arithmetic, quadratic reciprocity, Diophantine equations. The sort matters for divisibility (p ≠ 0) and modular arithmetic (n ≠ 0).

**Stair 5: Val/Combinatorics/** — Mathlib/Combinatorics/ (53,907 lines)

Graphs, partitions, generating functions. Less zero-management than algebra. The sort matters for counting (empty vs zero-count).

### Tier 5: Logic and foundations

**Stair 6: Val/SetTheory.lean** — Mathlib/SetTheory/ (19,486 lines)

Ordinals, cardinals, ZFC. The sort matters for the empty set (origin vs contents(∅)).

**Stair 7: Val/Logic.lean** — Mathlib/Logic/ (14,362 lines)

Propositional logic, first-order logic. Less zero-management. Mostly pure math.

**Stair 8: Val/Computability.lean** — Mathlib/Computability/ (14,993 lines)

Turing machines, decidability, halting problem. The sort matters for undecidability (origin = the computation that doesn't halt).

### Tier 6: Specialized domains

**Stair 9: Val/ModelTheory.lean** — Mathlib/ModelTheory/ (12,853 lines)

**Stair 10: Val/RepresentationTheory.lean** — Mathlib/RepresentationTheory/ (12,211 lines)

**Stair 11: Val/Dynamics.lean** — Mathlib/Dynamics/ (6,514 lines)

**Stair 12: Val/Condensed.lean** — Mathlib/Condensed/ (4,326 lines)

**Stair 13: Val/InformationTheory.lean** — Mathlib/InformationTheory/ (1,457 lines)

Each of these is small enough for a single file. Import the relevant foundation (Algebra, Analysis, etc.) and write domain-specific theorems.

## The Method

For each stair:

1. **Read the Mathlib subdirectory.** List all files. Count theorems. Identify which mention zero, ≠ 0, the 17 typeclasses.

2. **Categorize.** For each theorem:
   - Redundant (exists to manage zero) → skip
   - Simpler (statement loses hypotheses, proof shortens) → restate with Val
   - Unchanged (pure math) → restate, proof should be shorter because lemmas it calls got shorter

3. **Write the origin-lean file.** Import the base. Definitions and theorems only. Every proof calls the base. 80-150 lines per file.

4. **Build.** Under 1 second. Zero sorries.

5. **Count.** Mathlib lines vs origin-lean lines for the same theorems. The ratio predicts the next subdirectory.

## The Prediction

| | Mathlib | origin-lean (predicted) |
|---|---|---|
| Already covered | 1,634,804 lines | 10,615 lines (measured) |
| Data structures | 156,875 lines | ~4,000 lines |
| Group + Field theory | 78,452 lines | ~2,000 lines |
| Number theory + Combinatorics | 122,146 lines | ~3,000 lines |
| Logic + Foundations + Computability | 48,841 lines | ~1,500 lines |
| Specialized domains | 37,361 lines | ~1,500 lines |
| Infrastructure | ~66,000 lines | 0 (not math) |
| **Total** | **~2,160,000 lines** | **~23,000 lines** |

The ratio: ~2,160,000 → ~23,000. That's **99% reduction**.

The 98% reduction on foundational infrastructure (from origin-mathlib) becomes 99% on the full library because the compounding accelerates as you go up the stack. Every domain calls the base. Every proof is shorter. The foundation does the work.

## The Kill Switch

If any stair produces more lines than the Mathlib equivalent, the base is missing something. Step down. Strengthen Foundation or Algebra. Step back up.

If the prediction is wrong — if 23,000 becomes 50,000 or 100,000 — that's information. The ratio at each stair tells us where the compounding stops.

The honest test: build the first uncovered stair (Data/Nat/). Measure the ratio. If it holds, keep going. If it doesn't, the numbers say why.

## The Order

Always the lowest stair. Always build clean before stepping up. The dependency tree determines the order:

```
Foundation (done)
  → Algebra (done)
    → Data (Stair 1)
      → GroupTheory (Stair 2)
      → FieldTheory (Stair 3)
      → NumberTheory (Stair 4)
      → Combinatorics (Stair 5)
    → SetTheory (Stair 6)
    → Logic (Stair 7)
    → Computability (Stair 8)
    → Specialized (Stairs 9-13)
```

The foundation is done. The first uncovered stair is Data. Start there.
