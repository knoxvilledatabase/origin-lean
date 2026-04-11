# Step 3: Restate Mathlib Through the Val Foundation

## The Goal

Restate Mathlib's 88,494 theorems through the Val foundation. Every theorem either:
1. **Already exists** in Foundation or Algebra under a different name → deleted (it was duplication)
2. **Dissolves** because its `≠ 0` hypothesis or typeclass disappears → merged or trivial
3. **Genuinely new** domain-specific math → restated, proof shorter because the base is stronger

Zero duplication. Everything extends. Strip until it hurts.

## Where We Are

**10 files. 7,476 lines. 19 domains. All build clean.**

```
Val/
  Foundation.lean      268  — the type, ops, simp set
  Algebra.lean         716  — lifted laws + ring/field + ordered + vector + poly + functional + spectral
  Category.lean        968  — functors, monoidal, limits, preadditive, abelian, linear, enriched
  RingTheory.lean      962  — ideals, localization, Noetherian, Dedekind, graded, tensor, schemes
  LinearAlgebra.lean   504  — determinants, bilinear, modules, finite dim, matrices, projective, tensor
  Analysis.lean      2,302  — limits through asymptotic analysis (23 domains consolidated)
  MeasureTheory.lean   469  — measures, integrals, decomposition, specific constructions
  Topology.lean        878  — compactification through sheaves
  Applied.lean         199  — probability + homological algebra
  Geometry.lean        210  — algebraic + differential geometry
```

Every domain accessible in **2 reads** (Foundation + domain file). An AI extending any domain reads at most 2 files before working.

## Stair 0: Deduplication + Consolidation

Before adding new domains, we audited and consolidated the existing codebase in four phases.

### Phase 1: Deduplication (10,615 → 8,683 lines)

Audited 79 files for violations of "extend, never duplicate." Found 5 categories of duplication:

1. **17 duplicate unary maps** — all identical to `valMap`. Replaced with `abbrev` aliases.
2. **10 duplicate binary maps** — all identical to `mul`. Replaced with `abbrev` aliases.
3. **174 `_ne_origin` theorems** — all closable by Foundation's `@[simp] contents_ne_origin`. Deleted.
4. **41 redundant simp lemmas** — restating Foundation's simp set for `abbrev`'d functions. Deleted.
5. **~95 trivial `_exists` theorems** — all `⟨_, rfl⟩`. Foundation now has `contents_exists`. Deleted.

**Result:** 10,615 → 8,683 lines. 1,932 lines removed (18%). Same 79 files, same 19 domains.

### Phase 2: File Consolidation (79 files → 10 files, 8,683 → 7,476 lines)

Consolidated 79 files into 10. The principle: one file = one complete context for AI. No file hopping. Every domain accessible in 2 reads.

What moved where:
- RingField, OrderedField, VectorSpace, PolyRing, FunctionalAnalysis, SpectralTheory → **Algebra.lean** (all import only Algebra, so they're the "first layer")
- 9 Category/ files (minus Sheaf) → **Category.lean**
- 11 RingTheory/ files → **RingTheory.lean**
- 7 LinearAlgebra/ files → **LinearAlgebra.lean**
- 23 Analysis/ files → **Analysis.lean**
- 9 Topology/ files + Category/Sheaf → **Topology.lean**
- 7 MeasureTheory/ files → **MeasureTheory.lean**
- Probability + HomologicalAlgebra → **Applied.lean**
- AlgebraicGeometry + DifferentialGeometry → **Geometry.lean**

Cross-dependency resolution:
- Category/Sheaf → Topology.lean (breaks the Category ↔ Topology cycle)
- FunctionalAnalysis → Algebra.lean (Analysis imports Algebra, gets it for free)
- PolyRing → Algebra.lean (RingTheory imports Algebra, gets it for free)

**Result:** 8,683 → 7,476 lines. 1,207 lines removed (14%) — pure file boilerplate (imports, namespace, universe declarations repeated 79 times).

### Combined result

| Metric | Start | After dedup | After consolidation |
|---|---|---|---|
| Files | 79 | 79 | 10 |
| Lines | 10,615 | 8,683 | 7,476 |
| Domains | 19 | 19 | 19 |
| Reduction | — | 18% | 30% total |

**Status:** complete

---

## The Scans

Two scans determined the stair order. The first measured zero-management density. The second measured reusability.

### Scan 1: Zero-management density

| Domain | Files | Lines | Theorems | ≠ 0 refs | Typeclass refs | Zero density |
|---|---|---|---|---|---|---|
| InformationTheory | 6 | 1,457 | 112 | 16 | 1 | low |
| Condensed | 33 | 4,326 | 74 | 0 | 3 | none |
| Dynamics | 31 | 6,514 | 612 | 72 | 22 | low |
| RepresentationTheory | 37 | 12,211 | 746 | 37 | 96 | medium |
| ModelTheory | 34 | 12,853 | 883 | 12 | 31 | low |
| Computability | 34 | 14,993 | 1,060 | 29 | 5 | near zero |
| Logic | 57 | 14,362 | 1,415 | 23 | 1 | near zero |
| SetTheory | 46 | 19,486 | 2,401 | 344 | 28 | medium |
| FieldTheory | 78 | 26,919 | 2,056 | 696 | 363 | very high |
| GroupTheory | 160 | 51,533 | 3,686 | 370 | 223 | medium |
| Combinatorics | 170 | 53,907 | 4,516 | 257 | 84 | low |
| NumberTheory | 231 | 68,239 | 4,642 | 2,426 | 545 | very high |
| Data | 642 | 156,875 | 17,426 | 1,723 | 738 | medium |

### Scan 2: Reusability

| Domain | New Defs (Mathlib) | Genuinely new defs | % Covered by base |
|---|---|---|---|
| InformationTheory | 6 | 2 | 55% |
| Condensed | 60 | 21 | 56% |
| Dynamics | 43 | 23 | 53% |
| RepresentationTheory | 248 | 86 | 39% |
| FieldTheory | 198 | 89 | 53% |
| SetTheory | 174 | 104 | 23% |
| ModelTheory | 245 | 159 | 34% |
| Computability | 288 | 187 | 17% |
| Logic | 376 | 244 | 6% |
| NumberTheory | 461 | 253 | 47% |
| GroupTheory | 596 | 268 | 35% |
| Combinatorics | 598 | 358 | 30% |
| Data | 1,985 | 694 | 30% |

The three core operations (`valMap`, `mul`, `valPair`) absorb ~53% of all mathematical definitions across all domains.

## The Map

### Already covered (19 domains in 10 files)

| Mathlib directory | Mathlib lines | origin-lean file | Section |
|---|---|---|---|
| Algebra/ | 312,262 | Algebra.lean | Lifted Laws, Ring/Field |
| Analysis/ | 235,193 | Analysis.lean | 23 sections |
| CategoryTheory/ | 256,803 | Category.lean | 9 sections |
| Topology/ | 182,394 | Topology.lean | 10 sections |
| RingTheory/ | 175,123 | RingTheory.lean | 11 sections |
| LinearAlgebra/ | 102,475 | LinearAlgebra.lean | 7 sections |
| MeasureTheory/ | 113,074 | MeasureTheory.lean | 7 sections |
| Order/ | 95,034 | Algebra.lean | Ordered Field |
| Probability/ | 39,827 | Applied.lean | Probability |
| AlgebraicGeometry/ | 45,504 | Geometry.lean | Algebraic Geometry |
| Geometry/ | 51,622 | Geometry.lean | Differential Geometry |
| AlgebraicTopology/ | 26,493 | Applied.lean | Homological Algebra |
| **Subtotal** | **1,634,804** | **10 files, 7,476 lines** | |

### Not yet covered

| Mathlib directory | Lines | Genuinely new defs | Target file | What it is |
|---|---|---|---|---|
| InformationTheory | 1,457 | 2 | Applied.lean | Entropy, mutual information |
| Condensed | 4,326 | 21 | Category.lean | Condensed mathematics |
| Dynamics | 6,514 | 23 | Topology.lean | Ergodic theory, flows |
| RepresentationTheory | 12,211 | 86 | Algebra.lean | Group representations, characters |
| FieldTheory | 26,919 | 89 | Algebra.lean | Galois theory, splitting fields |
| SetTheory | 19,486 | 104 | Applied.lean | Ordinals, cardinals, ZFC |
| ModelTheory | 12,853 | 159 | Category.lean | Structures, ultraproducts |
| Computability | 14,993 | 187 | Applied.lean | Turing machines, decidability |
| Logic | 14,362 | 244 | Applied.lean | Propositional, first-order |
| NumberTheory | 68,239 | 253 | RingTheory.lean | Primes, modular arithmetic |
| GroupTheory | 51,533 | 268 | Algebra.lean | Group actions, Sylow |
| Combinatorics | 53,907 | 358 | Applied.lean | Graphs, partitions |
| Data | 156,875 | 694 | Data.lean (new) | Data structures, types |
| **Subtotal** | **443,675** | **2,488** | | |

### Infrastructure (not math, not restated)

| Mathlib directory | Lines | What it is |
|---|---|---|
| Tactic/ | ~50,000 | Custom tactics |
| Mathport/ + Deprecated/ + Testing/ + Util/ + Lean/ + Control/ | ~16,000 | Infrastructure |
| **Subtotal** | **~66,000** | **Not math. Not restated.** |

## The Stairs: Fewest New Definitions First

Each stair adds a **section** to an existing file — not a new file. The 10-file structure stays at 10 files (11 if Data earns its own). No file bloat. No new imports. Just sections extending the base.

Each stair builds clean before moving up. Each stair validates the ratio.

**Stair 1: InformationTheory** (1,457 Mathlib lines → ~60 new lines)

2 genuinely new definitions. Entropy, KL divergence, Hamming distance. Hamming norm is `valMap`. KL scaling guards dissolve. **Section in Applied.lean** (extends Probability).

**Status:** not started

**Stair 2: Condensed** (4,326 lines → ~60 lines)

21 genuinely new definitions. Condensed sets, condensed abelian groups, sheaf conditions. Zero `≠ 0` references. **Section in Category.lean** (extends categorical infrastructure).

**Status:** not started

**Stair 3: Dynamics** (6,514 lines → ~60 lines)

23 genuinely new definitions. Ergodic theory, topological dynamics, flows. Flow maps are `mul`. Solution curves are `valMap`. **Section in Topology.lean** (extends topological infrastructure).

**Status:** not started

**Stair 4: RepresentationTheory** (12,211 lines → ~70 lines)

86 genuinely new definitions. Group representations, characters, Maschke's theorem. Representations are `valMap`. Characters are trace = `valMap`. **Section in Algebra.lean** (extends algebraic infrastructure).

**Status:** not started

**Stair 5: FieldTheory** (26,919 lines → ~150 lines)

89 genuinely new definitions. **High dissolution**: 696 `≠ 0` refs, 363 typeclass refs. Galois theory, splitting fields, algebraic closures. Extensions and Galois actions are `valMap`. **Section in Algebra.lean**.

**Status:** not started

**Stair 6: SetTheory** (19,486 lines → ~150 lines)

104 genuinely new definitions. Ordinals, cardinals, ZFC. The sort matters for the empty set (origin vs contents(∅)). **Section in Applied.lean**.

**Status:** not started

**Stair 7: ModelTheory** (12,853 lines → ~120 lines)

159 genuinely new definitions. Structures, languages, ultraproducts. Interpretation maps are `valMap`. **Section in Category.lean**.

**Status:** not started

**Stair 8: Computability** (14,993 lines → ~140 lines)

187 genuinely new definitions. Turing machines, decidability, halting problem. Evaluation maps are `valMap`. **Section in Applied.lean**.

**Status:** not started

**Stair 9: Logic** (14,362 lines → ~130 lines)

244 genuinely new definitions. Propositional logic, first-order logic, encodability. Almost entirely new foundational infrastructure. **Section in Applied.lean**.

**Status:** not started

**Stair 10: NumberTheory** (68,239 lines → ~500 lines)

253 genuinely new definitions. **High dissolution**: 2,426 `≠ 0` refs, 545 typeclass refs. Primes, modular arithmetic, quadratic reciprocity. Arithmetic functions are `valMap`. **Section in RingTheory.lean**.

**Status:** not started

**Stair 11: GroupTheory** (51,533 lines → ~300 lines)

268 genuinely new definitions. Group actions, Sylow theorems, solvable groups. Conjugation and group actions are `valMap`. **Section in Algebra.lean**.

**Status:** not started

**Stair 12: Combinatorics** (53,907 lines → ~450 lines)

358 genuinely new definitions. Graphs, partitions, generating functions, Young tableaux. **Section in Applied.lean**.

**Status:** not started

**Stair 13: Data** (156,875 lines → ~800 lines)

694 genuinely new definitions. The biggest domain. Data structures, types, lists, sets, finsets, nat, int, rat, real, complex. The only stair that earns its own file: **Val/Data.lean** (11th file).

**Status:** not started

## The Method

For each stair:

1. **Scan.** Read the Mathlib subdirectory. For each theorem: already in the base (delete), dissolves (merge), or genuinely new (restate as section).

2. **Add section.** Open the target file. Add a section with definitions and theorems. Every proof calls the base. Zero duplication.

3. **Build.** Under 1 second. Zero sorries.

4. **Measure.** Lines added vs Mathlib lines. The ratio validates the prediction.

## The Prediction (revised after consolidation)

### Per-stair predictions

| Stair | Domain | Mathlib lines | New defs | Est. new lines | Target file |
|---|---|---:|---:|---:|---|
| 1 | InformationTheory | 1,457 | 2 | 60 | Applied.lean |
| 2 | Condensed | 4,326 | 21 | 60 | Category.lean |
| 3 | Dynamics | 6,514 | 23 | 60 | Topology.lean |
| 4 | RepresentationTheory | 12,211 | 86 | 70 | Algebra.lean |
| 5 | FieldTheory | 26,919 | 89 | 150 | Algebra.lean |
| 6 | SetTheory | 19,486 | 104 | 150 | Applied.lean |
| 7 | ModelTheory | 12,853 | 159 | 120 | Category.lean |
| 8 | Computability | 14,993 | 187 | 140 | Applied.lean |
| 9 | Logic | 14,362 | 244 | 130 | Applied.lean |
| 10 | NumberTheory | 68,239 | 253 | 500 | RingTheory.lean |
| 11 | GroupTheory | 51,533 | 268 | 300 | Algebra.lean |
| 12 | Combinatorics | 53,907 | 358 | 450 | Applied.lean |
| 13 | Data | 156,875 | 694 | 800 | Data.lean (new) |
| | **Total** | **443,675** | **2,488** | **2,990** | |

### Total prediction

| | Mathlib | origin-lean |
|---|---|---|
| Already covered (19 domains) | 1,634,804 | 7,476 (measured) |
| Uncovered (13 domains) | 443,675 | ~2,990 (predicted) |
| Infrastructure | ~66,000 | 0 (not math) |
| **Total** | **~2,160,000** | **~10,466** |

The ratio: ~2,160,000 → ~10,466. That's **99.5% reduction**.

The consolidation reduced the prediction from ~12,344 to ~10,466 — sections inside existing files have zero import/namespace overhead, so each stair is leaner than a standalone file would be.

**11 files covering all of Mathlib.** Every domain accessible in 2 reads.

## The Principle

Zero duplication. Everything extends. New domains don't create files — they add sections. If a theorem exists in the base, it doesn't get restated. If two sections prove the same pattern, the pattern belongs in the base.

Strip until it hurts. Then only add back what's necessary.

## The Order

```
Sorted by genuinely new definitions (fewest first):

  Stair 1:  InformationTheory    →  Applied.lean       +60 lines
  Stair 2:  Condensed            →  Category.lean      +60 lines
  Stair 3:  Dynamics             →  Topology.lean      +60 lines
  Stair 4:  RepresentationTheory →  Algebra.lean       +70 lines
  Stair 5:  FieldTheory          →  Algebra.lean      +150 lines
  Stair 6:  SetTheory            →  Applied.lean      +150 lines
  Stair 7:  ModelTheory          →  Category.lean     +120 lines
  Stair 8:  Computability        →  Applied.lean      +140 lines
  Stair 9:  Logic                →  Applied.lean      +130 lines
  Stair 10: NumberTheory         →  RingTheory.lean   +500 lines
  Stair 11: GroupTheory          →  Algebra.lean      +300 lines
  Stair 12: Combinatorics        →  Applied.lean      +450 lines
  Stair 13: Data                 →  Data.lean (new)   +800 lines
```

Fewest new definitions first. Sections, not files. Strip until it hurts. Hardest last.
