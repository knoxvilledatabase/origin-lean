# Step 4: Exhaustive Theorem Classification

## The Goal

Replace statistical calibration with exhaustive classification for all 173,646 Mathlib theorems. Every theorem individually classified. No sampling. No extrapolation.

The THEOREM_MAP.md currently has:
- 13 uncovered domains: classified theorem-by-theorem (done)
- 12 covered domains: classified by statistical calibration (not done)

This step finishes the 12 covered domains. Every theorem in every file, individually classified into B1, B2, or B3.

## What to Read First

1. **[THEOREM_MAP.md](THEOREM_MAP.md)** — the current map. Read the methodology section at the bottom. Understand the three buckets (B1: simp closes it, B2: ≠ 0 dissolves, B3: genuinely new). Read the 13 exhaustively-mapped domains to understand what good classification looks like.

2. **[Val/Foundation.lean](Val/Foundation.lean)** — the 44 simp lemmas. These define what B1 means: if a theorem is about constructor interactions that these simp lemmas handle, it's B1.

3. **[Val/Algebra.lean](Val/Algebra.lean)** — the lifted laws. Theorems about associativity, commutativity, distributivity lifted to Val α are B1. Theorems that call these laws are B1.

4. **The origin-mathlib checkout** at `/Users/tallbr00/Documents/venv/original-arithmetic/origin-mathlib/`. This has the full Mathlib source AND the Val stack side by side. Every theorem to classify is here.

## What NOT to Do

- **Do NOT write code** unless a theorem genuinely can't be classified without testing it. The goal is classification, not implementation.
- **Do NOT modify Foundation.lean or Algebra.lean.** If a theorem seems like it needs a new base method to classify as B1, note it in the classification but don't add it. That's a separate step.
- **Do NOT re-implement the Val stack.** The 79 files in origin-lean are the reference for what B3 looks like when restated. Don't re-do that work.
- **Do NOT sample.** Every theorem. Every file. No skipping.

## The 12 Domains to Classify

In order from smallest to largest (lowest hanging fruit first):

| # | Domain | Theorems | Files | Mathlib path |
|---|---|---|---|---|
| 1 | Order | ~9,500 | 304 | Mathlib/Order/ |
| 2 | LinearAlgebra | ~10,200 | 353 | Mathlib/LinearAlgebra/ |
| 3 | MeasureTheory | ~11,300 | 302 | Mathlib/MeasureTheory/ |
| 4 | Probability | ~4,000 | 128 | Mathlib/Probability/ |
| 5 | Geometry | ~5,200 | 129 | Mathlib/Geometry/ |
| 6 | AlgebraicGeometry | ~4,500 | 125 | Mathlib/AlgebraicGeometry/ |
| 7 | AlgebraicTopology | ~2,600 | 128 | Mathlib/AlgebraicTopology/ |
| 8 | Topology | ~18,200 | 639 | Mathlib/Topology/ |
| 9 | RingTheory | ~17,500 | 663 | Mathlib/RingTheory/ |
| 10 | Analysis | ~23,500 | 782 | Mathlib/Analysis/ |
| 11 | CategoryTheory | ~25,700 | 1,046 | Mathlib/CategoryTheory/ |
| 12 | Algebra | ~31,200 | 1,300 | Mathlib/Algebra/ |

Total: ~163,400 theorems across 5,899 files.

## The Method

For each domain, for each file, for each theorem:

### Step 1: Read the theorem statement

```lean
theorem mul_ne_zero (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0
```

### Step 2: Classify

**Is it B1?** Ask: is this about constructor interactions, algebraic identities, coercion wrappers, typeclass instances, definitional unfoldings, monotonicity, or lift lemmas? Would `by simp` close it on the Val foundation?

Examples of B1:
- `zero_mul : 0 * a = 0` — simp lemma, Foundation handles it
- `mul_assoc : a * b * c = a * (b * c)` — Algebra handles it
- `coe_mul : ↑(a * b) = ↑a * ↑b` — coercion wrapper, structural
- `MonoidHom.map_one : f 1 = 1` — typeclass instance, structural

**Is it B2?** Ask: does it carry `≠ 0`, `NeZero`, `NoZeroDivisors`, `Nontrivial`, `IsUnit`, `WithBot`/`WithTop`, `ae` (almost everywhere), `support = {i | f i ≠ 0}`, or any sentinel-zero convention? Would the hypothesis disappear if origin and contents(0) were distinct constructors?

Examples of B2:
- `mul_ne_zero (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0` — the ≠ 0 dissolves
- `inv_ne_zero (h : a ≠ 0) : a⁻¹ ≠ 0` — the ≠ 0 dissolves
- `div_self (h : a ≠ 0) : a / a = 1` — the ≠ 0 dissolves

**Is it B3?** Neither B1 nor B2. It states domain-specific mathematical content that needs to be expressed.

Examples of B3:
- `Nat.prime_def_lt_prime : ...` — domain-specific number theory
- `spectral_radius_le_norm : ...` — domain-specific functional analysis
- `dominated_convergence : ...` — domain-specific measure theory

### Step 3: Record

For each file, record:

```
Mathlib/Algebra/Ring/Basic.lean (47 theorems)
  B1: 31 (66%) — [list of theorem names]
  B2: 8 (17%) — [list of theorem names]
  B3: 8 (17%) — [list of theorem names]
```

### Step 4: Aggregate

After each domain is complete, update THEOREM_MAP.md:
- Replace "mapped by statistical calibration" with "mapped theorem-by-theorem"
- Update the counts
- Note any theorems that didn't fit cleanly (edge cases)

## The Output

THEOREM_MAP.md updated with exhaustive counts for all 25 domains. The grand totals either confirmed or corrected. The 99.5% compression claim either stands on exhaustive evidence or is revised to reflect what the data actually shows.

## The Order

One domain at a time. Start with the smallest (Order, ~9,500 theorems). This gives the fastest feedback on whether the method works at scale. Each domain completed before starting the next.

Within a domain: one subdirectory at a time. Each subdirectory is a natural unit. Complete it, record it, move on.

## How to Handle Edge Cases

Some theorems won't fit cleanly into one bucket:

- **Mixed B1/B2**: a theorem that's both structural plumbing AND carries ≠ 0. Classify as B2 (the ≠ 0 is the reason the theorem exists separately).
- **B3 that becomes B1 with a base method**: if a B3 theorem would become B1 if Foundation had one more simp lemma, classify as B3 and note: "would become B1 if Foundation added X." Don't add it. Note it.
- **Theorems about Mathlib infrastructure**: `simp` lemmas for Mathlib-specific types (e.g., `WithBot.coe_lt_coe`). Classify as B1 — they're structural plumbing for Mathlib's own types.

## Estimated Effort

Each file has ~10-50 theorems. Classification of one theorem takes seconds (read statement, check for ≠ 0 or structural pattern, classify). A file takes 5-15 minutes. A subdirectory (5-20 files) takes 1-2 hours.

The 12 domains have ~5,899 files. At ~10 minutes per file, that's ~1,000 hours of classification. With AI, parallelizable. Multiple sessions, each taking a domain.

This is the work that makes the claim rigorous. No shortcuts.

## The Principle

If the classification is honest, the numbers speak for themselves. If 51.9% is actually 45%, say 45%. If 32.7% is actually 40%, say 40%. The point is not to defend a prediction. The point is to know the truth.

The kill switch: if any domain shows more B3 than predicted, that's information. It means the compression is less than claimed in that domain. Document it honestly.
