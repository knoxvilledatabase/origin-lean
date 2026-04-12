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

## The Convergence Hypothesis

Every cycle of write → audit → strengthen base → measure has contracted the codebase:

| Cycle | Action | Before | After | Contraction |
|---|---|---|---|---|
| 1 | Deduplication | 10,615 | 8,683 | 18% |
| 2 | Consolidation | 8,683 | 7,476 | 14% |
| 3 | Add stairs + audit | 10,885 | 9,931 | 9% |
| 4 | Base strengthening | 9,931 | 10,050 | (base grew, domains will shrink) |

The pattern: the base gets stronger, the domains get thinner, the next domain is cheaper. This compounds.

If the lines-per-B3-theorem decreases with each stair because the base absorbs more patterns:

| Lines/theorem | Total B3 lines | + Foundation | Grand total | Reduction |
|---|---|---|---|---|
| 2.5 (current estimate) | 142,038 | 10,050 | 152,088 | 93.0% |
| 2.0 (after 5 stairs) | 113,630 | 10,050 | 123,680 | 94.3% |
| 1.5 (after 10 stairs) | 85,223 | 10,050 | 95,273 | 95.6% |
| 1.0 (convergence limit?) | 56,815 | 10,050 | 66,865 | 96.9% |

And if B3 theorems reclassify to B1 as the base strengthens (we've already seen ~1,160 reclassify from one scan):

| B3 remaining | Lines/thm | Total lines | Reduction |
|---|---|---|---|
| 56,815 (current) | 2.5 | 152,088 | 93.0% |
| 50,000 (after reclassification) | 2.0 | 110,050 | 94.9% |
| 45,000 | 1.5 | 77,550 | 96.4% |
| 40,000 | 1.2 | 58,050 | 97.3% |
| 35,000 (aggressive reclassification) | 1.0 | 45,050 | 97.9% |

**The convergence limit may approach 97-98% reduction.** Each stair tells us where the curve levels off.

## The Stair Steps: Smallest First, Measure the Contraction

The order is smallest B3 count first. Each stair teaches the base something. The base strengthening compounds. By the time we reach the big domains, the base is so strong they collapse.

### The cycle (for every stair)

1. **Strengthen the base** — scan this domain's B3 for patterns that repeat 5+ times across domains. Add to Foundation or Algebra. Build. Audit.
2. **Write the B3 theorems** — translate each B3 theorem to Val-style. Add as section in existing file. No new files. No duplication.
3. **Audit** — `./scripts/audit.sh`. Delete anything caught. `lake build`.
4. **Measure** — record three numbers:
   - Lines added for this domain
   - Lines removed (audit + reclassification)
   - **Net lines per B3 theorem** — the efficiency metric
5. **Plot** — the net lines/theorem should decrease. The curve predicts the final total.

### The stairs

| Stair | Domain | B3 | Cumulative B3 | Status |
|---|---|---|---|---|
| 1 | InformationTheory | 41 | 41 | not started |
| 2 | Condensed | 54 | 95 | not started |
| 3 | Dynamics | 203 | 298 | not started |
| 4 | ModelTheory | 282 | 580 | not started |
| 5 | RepresentationTheory | 399 | 979 | not started |
| 6 | SetTheory | 416 | 1,395 | not started |
| 7 | Computability | 649 | 2,044 | not started |
| 8 | FieldTheory | 970 | 3,014 | not started |
| 9 | GroupTheory | 1,199 | 4,213 | not started |
| 10 | Combinatorics | 2,749 | 6,962 | not started |
| 11 | NumberTheory | 3,117 | 10,079 | not started |
| 12 | RingTheory + LinearAlgebra | 6,191 | 16,270 | not started |
| 13 | CategoryTheory + AlgTop | 3,530 | 19,800 | not started |
| 14 | Geometry + AlgGeom | 3,496 | 23,296 | not started |
| 15 | MeasureTheory + Probability | 4,077 | 27,373 | not started |
| 16 | Data | 4,222 | 31,595 | not started |
| 17 | Topology + Order | 8,011 | 39,606 | not started |
| 18 | Analysis | 8,057 | 47,663 | not started |
| 19 | Algebra | 9,152 | 56,815 | not started |

### The measurement table (filled in as we go)

| Stair | Domain | B3 written | Lines added | Lines removed | Net lines | Lines/thm | Cumulative total |
|---|---|---|---|---|---|---|---|
| 1 | InformationTheory | 41 | 427 | 0 | 427 | 10.4 | 10,477 |
| 2 | Condensed | 49 | 320 | 0 | 320 | 6.5 | 10,797 |
| 3 | Dynamics | 205 | 976 | 0 | 976 | 4.7 | 11,773 |
| ... | ... | | | | | | |
| 19 | Algebra | | | | | | |

**Stair 1 notes:** 10.4 lines/theorem is the baseline. This includes definitions (`klFunVal`, `klFunMap`), section headers, docstrings, and structure. The pure theorem-to-proof ratio is lower (~3-4 lines) but the overhead of organizing domain content into readable sections adds lines. The question: does this ratio decrease as the base absorbs patterns and later domains need fewer new definitions?

The lines/thm column tells the story. If it trends downward, the convergence hypothesis holds. The final total is wherever the curve levels off.

### Milestone checkpoints

| Milestone | Stair | B3 covered | When to assess |
|---|---|---|---|
| **Pattern established** | 3 | 298 | Is lines/thm decreasing? If yes, continue. If no, diagnose. |
| **Convergence visible** | 8 | 3,014 | Plot the curve. Predict the final total. |
| **Half coverage** | 14 | 23,296 | Prediction should be stable. Is it below 100K? Below 80K? |
| **MVP for energy testing** | 18 | 47,663 | Analysis + Algebra + most domains. Test the hypothesis. |
| **Complete** | 19 | 56,815 | The final number. The honest answer. |

### Why biggest domains go last

Writing Algebra (9,152 B3) first at 2.5 lines/theorem = ~23,000 lines.
Writing Algebra last at 1.5 lines/theorem = ~14,000 lines.
Writing Algebra last at 1.0 lines/theorem = ~9,000 lines.

That's 14,000 lines saved just by ordering correctly. The base learns from 18 domains before touching Algebra. Every pattern has been absorbed. Every duplication has been caught. The biggest domain gets the strongest base.

## The Kill Switch

If the lines/theorem metric **increases** over three consecutive stairs, the convergence hypothesis is wrong. The base isn't getting stronger. Stop and diagnose.

If the total exceeds 200,000 lines, the prediction is wrong. Update honestly.

If the lines/theorem plateaus above 2.0, the final total will be ~120,000-150,000 (93-94% reduction). Still extraordinary. But not 99%.

If it plateaus below 1.5, the final total will be ~75,000-95,000 (95-96% reduction). Getting close.

If it keeps dropping below 1.0, the convergence limit might reach 97-98%. The curve tells us. We don't assume. We measure.

## The Deliverable

When complete:
- **~12 files** covering all of mathematics
- **Zero duplication** (verified by audit script at every stair)
- **Zero `≠ 0` hypotheses** (dissolved by origin/contents)
- **Zero typeclass infrastructure** (explicit parameters)
- **Every theorem justified** against the base
- **Measured contraction rate** at every stair
- **Plotted convergence curve** showing the trend
- **The final number** — the honest answer to "how many lines does it take?"

## The Purpose

This is not about code elegance. This is not about proving mathematicians wrong. This is not about competing with Mathlib.

This is about a dad who wondered why AI drinks so much water.

The 97 patches in the README are 97 branches on silicon. The 26,674 B2 theorems are 26,674 of those branches in mathematics alone. The 90,161 B1 theorems are the plumbing cost of not having the DRY principle at the foundation.

origin-lean is the DRY principle applied to mathematics, built by AI, for AI, so the next generation of models can learn math with less energy, less heat, less water.

Strip until it hurts. Then count the water you saved.
