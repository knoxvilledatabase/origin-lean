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

78 files. 26,919 lines. 2,056 theorems. Sorted by zero-management density (≠ 0 refs + typeclass refs per theorem, descending).

**Top 20 (highest density — most reduction expected):**

| File | Lines | Theorems | ≠ 0 | TC | Density | Per-thm |
|---|---|---|---|---|---|---|
| KummerPolynomial.lean | 127 | 10 | 27 | 1 | 28 | 280% |
| JacobsonNoether.lean | 200 | 5 | 8 | 5 | 13 | 260% |
| SeparablyGenerated.lean | 327 | 11 | 19 | 1 | 20 | 181% |
| RatFunc/Degree.lean | 126 | 12 | 20 | 0 | 20 | 166% |
| RatFunc/Basic.lean | 1,141 | 88 | 81 | 62 | 143 | 162% |
| Galois/NormalBasis.lean | 130 | 2 | 3 | 0 | 3 | 150% |
| SplittingField/Construction.lean | 312 | 13 | 12 | 7 | 19 | 146% |
| KummerExtension.lean | 558 | 30 | 42 | 1 | 43 | 143% |
| RatFunc/Defs.lean | 227 | 14 | 16 | 4 | 20 | 142% |
| RatFunc/Luroth.lean | 679 | 59 | 74 | 4 | 78 | 132% |
| IsSepClosed.lean | 315 | 17 | 18 | 3 | 21 | 123% |
| AbelRuffini.lean | 341 | 21 | 25 | 0 | 25 | 119% |
| PolynomialGaloisGroup.lean | 378 | 16 | 17 | 2 | 19 | 118% |
| IsAlgClosed/AlgebraicClosure.lean | 229 | 7 | 1 | 7 | 8 | 114% |
| AxGrothendieck.lean | 247 | 7 | 1 | 7 | 8 | 114% |
| IsAlgClosed/Basic.lean | 575 | 43 | 29 | 19 | 48 | 111% |
| Finite/Valuation.lean | 37 | 2 | 1 | 1 | 2 | 100% |
| Minpoly/Field.lean | 352 | 32 | 19 | 11 | 30 | 93% |
| Minpoly/Basic.lean | 293 | 26 | 15 | 9 | 24 | 92% |
| Minpoly/IsIntegrallyClosed.lean | 299 | 20 | 14 | 4 | 18 | 90% |

**Middle 30 (moderate density):**

| File | Lines | Theorems | ≠ 0 | TC | Density | Per-thm |
|---|---|---|---|---|---|---|
| PrimitiveElement.lean | 412 | 19 | 17 | 0 | 17 | 89% |
| Fixed.lean | 400 | 26 | 3 | 20 | 23 | 88% |
| Finite/Polynomial.lean | 226 | 13 | 0 | 10 | 10 | 76% |
| Separable.lean | 781 | 81 | 35 | 25 | 60 | 74% |
| Galois/IsGaloisGroup.lean | 500 | 35 | 4 | 22 | 26 | 74% |
| Finite/Extension.lean | 176 | 10 | 7 | 0 | 7 | 70% |
| RatFunc/AsPolynomial.lean | 406 | 43 | 24 | 4 | 28 | 65% |
| IsAlgClosed/Spectrum.lean | 185 | 13 | 3 | 4 | 7 | 53% |
| Finite/Basic.lean | 835 | 71 | 24 | 12 | 36 | 50% |
| Differential/Basic.lean | 196 | 12 | 6 | 0 | 6 | 50% |
| Finite/Trace.lean | 74 | 4 | 2 | 0 | 2 | 50% |
| Tower.lean | 64 | 2 | 0 | 1 | 1 | 50% |
| Normal/Basic.lean | 298 | 13 | 6 | 0 | 6 | 46% |
| Minpoly/MinpolyDiv.lean | 224 | 18 | 5 | 3 | 8 | 44% |
| Isaacs.lean | 128 | 7 | 3 | 0 | 3 | 42% |
| IsRealClosed/Basic.lean | 127 | 10 | 4 | 0 | 4 | 40% |
| PerfectClosure.lean | 507 | 22 | 0 | 9 | 9 | 40% |
| Finite/GaloisField.lean | 337 | 18 | 6 | 1 | 7 | 38% |
| SeparableDegree.lean | 916 | 70 | 26 | 0 | 26 | 37% |
| Minpoly/IsConjRoot.lean | 394 | 34 | 8 | 3 | 11 | 32% |
| IsPerfectClosure.lean | 548 | 61 | 0 | 19 | 19 | 31% |
| IsAlgClosed/Classification.lean | 203 | 7 | 0 | 2 | 2 | 28% |
| SplittingField/IsSplittingField.lean | 200 | 16 | 4 | 0 | 4 | 25% |
| IntermediateField/Adjoin/Basic.lean | 794 | 73 | 16 | 2 | 18 | 24% |
| NormalizedTrace.lean | 259 | 18 | 4 | 0 | 4 | 22% |
| Galois/Basic.lean | 702 | 41 | 4 | 5 | 9 | 21% |
| ChevalleyWarning.lean | 196 | 5 | 1 | 0 | 1 | 20% |
| Perfect.lean | 488 | 60 | 2 | 10 | 12 | 20% |
| Laurent.lean | 111 | 11 | 0 | 2 | 2 | 18% |
| PurelyInseparable/Basic.lean | 694 | 52 | 1 | 8 | 9 | 17% |

**Bottom 28 (low or zero density — mostly pure math):**

| File | Lines | Theorems | ≠ 0 | TC | Density | Per-thm |
|---|---|---|---|---|---|---|
| AlgebraicClosure.lean | 222 | 20 | 3 | 0 | 3 | 15% |
| Finiteness.lean | 106 | 8 | 0 | 1 | 1 | 12% |
| PurelyInseparable/Exponent.lean | 353 | 25 | 2 | 1 | 3 | 12% |
| Minpoly/ConjRootClass.lean | 203 | 25 | 3 | 0 | 3 | 12% |
| Extension.lean | 374 | 26 | 3 | 0 | 3 | 11% |
| Normal/Closure.lean | 315 | 26 | 3 | 0 | 3 | 11% |
| Normal/Defs.lean | 259 | 18 | 2 | 0 | 2 | 11% |
| PurelyInseparable/Tower.lean | 298 | 18 | 1 | 1 | 2 | 11% |
| IntermediateField/Basic.lean | 911 | 91 | 1 | 9 | 10 | 10% |
| IntermediateField/Adjoin/Algebra.lean | 369 | 34 | 1 | 2 | 3 | 8% |
| SeparableClosure.lean | 509 | 51 | 4 | 0 | 4 | 7% |
| IntermediateField/Algebraic.lean | 165 | 17 | 0 | 1 | 1 | 5% |
| CardinalEmb.lean | 354 | 20 | 1 | 0 | 1 | 5% |
| IntermediateField/Adjoin/Defs.lean | 772 | 114 | 0 | 1 | 1 | 0% |
| Relrank.lean | 538 | 106 | 0 | 0 | 0 | 0% |
| PurelyInseparable/PerfectClosure.lean | 432 | 31 | 0 | 0 | 0 | 0% |
| LinearDisjoint.lean | 763 | 68 | 0 | 0 | 0 | 0% |
| KrullTopology.lean | 336 | 12 | 0 | 0 | 0 | 0% |
| Galois/Profinite.lean | 347 | 13 | 0 | 0 | 0 | 0% |
| Galois/Infinite.lean | 291 | 11 | 0 | 0 | 0 | 0% |
| Galois/GaloisClosure.lean | 156 | 8 | 0 | 0 | 0 | 0% |
| Galois/Abelian.lean | 71 | 4 | 0 | 0 | 0 | 0% |
| Differential/Liouville.lean | 212 | 2 | 0 | 0 | 0 | 0% |
| Cardinality.lean | 70 | 5 | 0 | 0 | 0 | 0% |
| PrimeField.lean | 60 | 2 | 0 | 0 | 0 | 0% |
| MvRatFunc/Rank.lean | 40 | 1 | 0 | 0 | 0 | 0% |
| AbsoluteGaloisGroup.lean | 66 | 0 | 0 | 0 | 0 | 0% |
| Galois/Notation.lean | 53 | 0 | 0 | 0 | 0 | 0% |

**Totals:** 78 files, 26,919 lines, 2,056 theorems, 696 ≠ 0 refs, 363 typeclass refs

**Status:** complete

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
