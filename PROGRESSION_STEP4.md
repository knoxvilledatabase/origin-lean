# Step 4: Exhaustive Theorem Mapping

## The Goal

Validate the 99.5% reduction claim with evidence, not projection.

Step 3 built the structure — 11 files, 10,885 lines, 32 domains, all build clean. But the claim that these 10,885 lines cover all of Mathlib's 88,494 theorems is based on scans and ratios, not exhaustive verification.

Step 4 is the exhaustive verification. For every theorem in Mathlib, attempt it through the Val foundation and record which bucket it falls into.

## The Three Buckets

Every Mathlib theorem falls into exactly one:

**Bucket 1: Already a simp consequence.** The theorem is provable by `by simp` with Foundation's existing simp lemmas. No new code needed. The theorem doesn't exist in origin-lean because the simp set already knows it. This is the bulk of the reduction.

**Bucket 2: Dissolves.** The theorem exists in Mathlib only because of a `≠ 0` guard or one of the 17 zero-management typeclasses. In origin-lean, the hypothesis disappears and the theorem either merges with bucket 1 (simp closes it) or becomes trivially shorter.

**Bucket 3: Genuinely new.** The theorem states domain-specific mathematical content that no amount of simp lemmas or sort dispatch can handle. This is real math. This needs real code — either it already exists in origin-lean's domain sections, or it gets added.

The ratio of bucket 1+2 to bucket 3 is the actual measured reduction. This is what validates or falsifies the 99.5% claim.

## The Method

### Per-file approach

Work by Mathlib file, not by individual theorem. Files are organized by topic. Topics tend to fall into the same bucket.

For each Mathlib file:

1. **Read the file.** List every `theorem` and `lemma` declaration.
2. **Attempt each theorem.** Translate to Val-style (explicit parameters, no typeclasses). Try `by simp`. If that closes it → bucket 1. If the `≠ 0` hypothesis dissolves → bucket 2. If neither → bucket 3.
3. **Record the split.** File name, total theorems, bucket 1 count, bucket 2 count, bucket 3 count.
4. **For bucket 3 theorems:** Check if origin-lean already has it in the domain section. If yes, confirmed. If no, add it or note the gap.

### Domain-level approach

Process one Mathlib domain at a time. Sort domains by expected yield — the domain where the base handles the highest percentage of theorems goes first.

### The output

A table per domain, a running total across domains. The evidence is the table, not the code.

```
| Mathlib file | Theorems | Bucket 1 (simp) | Bucket 2 (dissolves) | Bucket 3 (new) |
|---|---|---|---|---|
| FieldTheory/Basic.lean | 47 | 38 | 6 | 3 |
| FieldTheory/Galois.lean | 62 | 41 | 14 | 7 |
| ... | | | | |
| **Total** | **2,056** | **?** | **?** | **?** |
```

## Starting Domain: FieldTheory

FieldTheory is the lowest hanging fruit for exhaustive mapping:

- **51% zero-management density** — highest ratio of `≠ 0` + typeclass refs to total theorems
- **2,056 theorems** — manageable size for exhaustive mapping
- **89 genuinely new definitions** — small bucket 3
- **78 Mathlib files, 26,919 lines** — collapses to a section in Algebra.lean

The prediction: ~1,800 theorems are bucket 1+2, ~256 are bucket 3. If this holds, the ratio is validated for the densest zero-management domain.

### Step 1: Scan FieldTheory files

List all 78 files. For each: file name, line count, theorem count, `≠ 0` ref count. Sort by `≠ 0` density descending. The densest files go first — they're where the base does the most work.

**Status:** not started

### Step 2: Map the densest files

Take the top 10 files by `≠ 0` density. For each theorem, attempt through Val. Record buckets.

**Status:** not started

### Step 3: Map the remaining files

Work through the rest. The pure math files (low `≠ 0` density) will have more bucket 3. That's expected — those are the genuinely new theorems.

**Status:** not started

### Step 4: Measure and report

Total bucket split. Compare against the prediction. Update PROGRESSION_STEP3.md with actuals instead of estimates.

**Status:** not started

## After FieldTheory

The next domain depends on the results. If the ratio holds for FieldTheory, pick the next highest-yield domain (NumberTheory at 64% density, but 4,642 theorems — larger). If the ratio breaks, diagnose why before continuing.

## Domain Priority (by expected yield)

| Domain | Theorems | ≠ 0 + TC density | Expected bucket 1+2 % |
|---|---|---|---|
| FieldTheory | 2,056 | 51% | ~85-90% |
| NumberTheory | 4,642 | 64% | ~85-90% |
| Data | 17,426 | 14% | ~70-80% |
| GroupTheory | 3,686 | 16% | ~70-80% |
| SetTheory | 2,401 | 15% | ~65-75% |
| RepresentationTheory | 746 | 18% | ~70-80% |
| Dynamics | 612 | 15% | ~70-80% |
| Combinatorics | 4,516 | 8% | ~60-70% |
| InformationTheory | 112 | 15% | ~70-80% |
| ModelTheory | 883 | 5% | ~50-60% |
| Condensed | 74 | 4% | ~50-60% |
| Computability | 1,060 | 3% | ~40-50% |
| Logic | 1,415 | 2% | ~30-40% |

Note: `≠ 0` + TC density alone doesn't predict bucket 1+2 percentage. Many theorems without `≠ 0` are still simp consequences (basic algebraic identities, constructor interactions). The expected percentages account for this — even low-density domains have substantial bucket 1 because the simp set handles all sort dispatch.

## The Kill Switch

If any domain's actual bucket 3 exceeds the predicted origin-lean lines for that domain, either:
1. The base is missing simp lemmas → strengthen Foundation, re-run
2. The domain has genuinely irreducible complexity → update the prediction honestly

The numbers say what they say. The honest answer is the only answer.

## The Principle

The exhaustive mapping isn't about writing code. It's about proving that code doesn't need to be written. Every theorem in bucket 1 is evidence that the simp set does the work. Every theorem in bucket 2 is evidence that the sort system dissolves the hypothesis. Every theorem in bucket 3 is the honest boundary of the claim.

Strip until it hurts. Then count what's left.
