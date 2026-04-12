# Step 5: Complete the Training Corpus

## The Purpose

origin-lean exists to prove that AI can learn all of mathematics from a fraction of the data, with a fraction of the energy, using a fraction of the water.

The target: a complete formal mathematics library that does everything Mathlib does, with zero redundancy, optimized for silicon consumption. Not a smaller library for humans to read — a **smaller training signal** for AI to learn from.

Every duplicate theorem is a redundant weight in a model. Every `≠ 0` hypothesis is a branch instruction on silicon. Every coercion wrapper is noise in the training data. origin-lean eliminates all of them.

## Where We Are

**11 files. 10,050 lines. 32 domains. All build clean.**

The exhaustive mapping of Mathlib's 173,646 theorems proved:
- **90,161 (51.9%)** are structural plumbing — absorbed by Val's simp set and constructor dispatch
- **26,674 (15.4%)** are zero-management — dissolved by origin/contents distinction
- **56,815 (32.7%)** are genuinely new mathematics — the irreducible content

**67.3% of Mathlib is infrastructure.** origin-lean eliminates it by construction.

The 10,050 lines are the foundation + domain structure + key results. The remaining work: state and prove the 56,815 genuinely new theorems on this foundation.

## What We Learned (Session Lessons)

These lessons were learned through building, breaking, rebuilding, and mapping. They are load-bearing. Any AI agent continuing this work must internalize them.

### 1. Not one line without justification

Every line of code must produce behavior that no other line already produces. If `by simp` can produce the behavior, the theorem doesn't exist. If another theorem already states it, the duplicate doesn't exist. The simp set is the source of truth.

We found duplication three times:
- First audit: 28 duplicate definitions, 316 duplicate theorems (10,615 → 8,683 lines)
- After adding 13 stairs: 203 more duplicates found (10,885 → 9,972 lines)
- After audit script: 11 more found (9,972 → 9,931 lines)

**Automation:** `./scripts/audit.sh` catches mechanical duplicates. Run it after every change. The human shouldn't need to ask "are you sure?" — the script asks automatically.

### 2. Strengthen the base before extending

Every time we extended to a new domain before strengthening the base, we produced duplication. Every time we strengthened first, the domain collapsed to one-liners.

The cycle: **strengthen → write → audit → repeat.** Never skip the strengthen step. The cost of skipping is duplication that compounds through every downstream domain.

Base additions that cascaded across all domains:
- `valMap` (Foundation): eliminated 17 duplicate unary map definitions
- `valPair` (Foundation): eliminated cross-type pairing duplication
- `contents_ne_origin` (Foundation @[simp]): eliminated 174 `_ne_origin` theorems
- `contents_exists` (Foundation): eliminated ~95 trivial `_exists` theorems
- `valMap_injective/surjective` (Foundation): eliminated injective-lifting patterns
- `valMap_preserves_mul/add/neg_general` (Algebra): eliminated homomorphism lifting patterns
- `valMap_preserves_smul` (Algebra): eliminated action preservation patterns
- `valPair_valMap` (Foundation): eliminated component-wise operation patterns
- `contents_congr` (Foundation @[simp]): eliminated 58 `show contents X = contents Y; rw [h]` patterns
- Sort-predicate interaction lemmas (Foundation @[simp]): connected sort predicates to operations

### 3. Consolidate for silicon, not humans

79 files → 11 files. One file per domain context. Every domain accessible in 2 reads (Foundation + domain file). An AI extending any domain reads at most 2 files before working.

The principle: every file boundary is a context switch for AI. Fewer files = fewer reads = faster understanding = less compute.

New domains don't create files — they add sections to existing files. The 11-file structure stays at 11 (plus Data.lean = 12 when Data earns its own file).

### 4. The three buckets

Every Mathlib theorem falls into exactly one:

- **Bucket 1 (51.9%): Structural plumbing.** Simp lemmas, coercion wrappers, typeclass instances, definitional unfoldings, monotonicity wrappers, lift lemmas, `rfl`/`by simp` closures. Val's simp set and constructor dispatch absorb these. They don't exist in origin-lean.

- **Bucket 2 (15.4%): Zero-management.** `≠ 0` guards, `NeZero` instances, `WithBot`/`WithTop`, `ae` (almost everywhere), `IsUnit`, `support = {i | f i ≠ 0}`, sentinel-zero conventions (`orderOf` returning 0 for infinite order), `NeBot` (the topological zero). Val's origin/contents distinction dissolves these. They don't exist in origin-lean.

- **Bucket 3 (32.7%): Genuinely new mathematics.** Galois theory, modular forms, graph coloring, Turing machines, Pell equations, Hensel's lemma, the chain rule, spectral theory. These need real proofs in any foundation. They exist in origin-lean, but shorter (no typeclass overhead, no `≠ 0` hypotheses, `by simp` handles sort dispatch).

### 5. The honest numbers

| Metric | Claim | Evidence |
|---|---|---|
| Line reduction | 93% | 10,050 lines (foundation) + ~140,000 lines (B3 theorems) = ~150,000 vs 2,160,000 |
| Theorem elimination | 67.3% | 116,835 of 173,646 theorems are infrastructure |
| Zero-management dissolution | 15.4% | 26,674 theorems exist solely for `≠ 0` boundary management |
| Structural plumbing absorption | 51.9% | 90,161 theorems are simp/rfl/wrapper/coercion |

The 99.5% number was the foundation's line count vs Mathlib's line count. The 93% is the complete restatement prediction. The 67.3% is the theorem elimination rate. Be precise about which metric you're citing.

### 6. Zero-management hotspots

Where Val's sort dispatch matters most (B2 concentration by domain):

| Domain | B2 % | What gets dissolved |
|---|---|---|
| RingTheory+LinearAlgebra | 36.8% | NonZeroDivisors, IsUnit, det ≠ 0, IsDomain |
| MeasureTheory+Probability | 26.1% | ae, null sets, NeZero measures |
| InformationTheory | 20.3% | KL divergence singularity, Hamming norm |
| Analysis | 15.8% | derivative at ≠ 0, power functions, L'Hopital |
| Geometry+AlgebraicGeometry | 15.3% | Euclidean angle vectors ≠ 0, elliptic curve coordinates |
| NumberTheory | 15.2% | p-adic valuations, cyclotomic NeZero, ramification |
| Algebra | 14.6% | GroupWithZero, polynomial degree, field division |
| Order | 14% | WithBot, WithTop, NeBot filters |

### 7. The DRY principle at mathematical scale

The 97 patches in the original-arithmetic README are the same boundary check written 97 different ways across math, logic, computation, and physics. Mathlib's 26,674 B2 theorems are 26,674 instances of the same boundary written 26,674 ways within mathematics alone.

origin-lean writes it once: `origin`. Three constructors. Four rules. The DRY principle applied to the AI water consumption problem.

## The Stair Steps

### Priority order: AI inference impact

Not all 56,815 B3 theorems contribute equally to AI performance. The domains most used in AI inference are:

1. **Analysis** (8,057 B3) — neural network math, optimization, convergence
2. **Algebra** (9,152 B3) — symbolic reasoning, algebraic manipulation
3. **Data** (4,222 B3) — data structures, lists, sets, natural numbers
4. **Topology + Order** (8,011 B3) — continuity, lattice theory, convergence
5. **LinearAlgebra** (~2,888 B3) — matrix operations, eigenvalues, linear systems
6. **MeasureTheory + Probability** (4,077 B3) — probabilistic reasoning, integration
7. **RingTheory** (~3,304 B3) — polynomial arithmetic, ideal theory
8. **CategoryTheory** (~3,087 B3) — compositional reasoning, functorial patterns
9. **NumberTheory** (3,117 B3) — modular arithmetic, primality
10. **Combinatorics** (2,749 B3) — graph theory, counting
11. **Geometry + AlgebraicGeometry** (3,496 B3) — geometric reasoning
12. **FieldTheory** (970 B3) — field extensions, Galois theory
13. **GroupTheory** (1,199 B3) — symmetry, permutations
14. **Computability** (649 B3) — decidability, recursion
15. **AlgebraicTopology** (~443 B3) — homological algebra
16. **SetTheory** (416 B3) — ordinals, cardinals
17. **RepresentationTheory** (399 B3) — group representations
18. **ModelTheory** (282 B3) — first-order logic, structures
19. **Dynamics** (203 B3) — ergodic theory, flows
20. **Condensed** (54 B3) — condensed mathematics
21. **InformationTheory** (41 B3) — entropy, divergence

### The execution cycle

For each domain, in priority order:

**1. Strengthen the base**
- Scan the domain's B3 theorems for patterns that repeat 5+ times
- If a pattern appears across multiple domains, add it to Foundation or Algebra
- Build and audit

**2. Write the B3 theorems**
- For each B3 theorem from the exhaustive mapping:
  - Translate to Val-style (explicit parameters, no typeclasses)
  - Prove: `by simp`, one-liner calling base, or short proof
  - Add as a section in the appropriate file
- No new files. Sections in existing files.
- No duplication. Every theorem checked against the base.

**3. Audit**
- `./scripts/audit.sh`
- If duplicates found, delete them
- `lake build`

**4. Measure**
- Lines added vs B3 theorems covered
- Average lines per theorem (target: 2.5)
- Running total toward 56,815

**5. Next domain**

### Milestone checkpoints

| Milestone | B3 covered | Est. total lines | Domains |
|---|---|---|---|
| MVP (testable) | ~12,000 | ~40,000 | Analysis + Algebra + Data |
| Core AI domains | ~25,000 | ~72,000 | + Topology + LinAlg + MeasureTheory |
| Extended coverage | ~40,000 | ~110,000 | + RingTheory + CategoryTheory + NumberTheory |
| Complete | 56,815 | ~150,000 | All domains |

The MVP milestone (~12,000 B3 theorems, ~40,000 lines) is enough to test the hypothesis: **train a model on origin-lean's Analysis + Algebra + Data vs Mathlib's equivalent, and measure energy consumption.**

### The deliverable

When complete:
- **~12 files, ~150,000 lines** covering all of mathematics
- **Zero duplication** (verified by audit script)
- **Zero `≠ 0` hypotheses** (dissolved by origin/contents)
- **Zero typeclass infrastructure** (explicit parameters)
- **Every theorem justified** against the base
- **67.3% fewer theorems** than Mathlib for the same coverage
- **93% fewer lines** than Mathlib
- **Testable hypothesis**: does training on this corpus reduce AI energy consumption?

## The Kill Switch

If any domain's B3 theorems require more lines than the Mathlib equivalent, the base is missing something. Step down. Strengthen the base. Step back up.

If the total exceeds 200,000 lines, the 93% prediction is wrong. Update the numbers honestly.

If an AI trained on origin-lean performs worse than one trained on Mathlib, the hypothesis is falsified. Report it honestly.

The numbers say what they say. The honest answer is the only answer.

## The Principle

Code is a liability, not an asset. Every line you write is a line that costs energy. The behavior the code produces is the asset. The code itself is the heat.

Strip until it hurts. Then count the water you saved.
