# File Management Plan: Split for AI Efficiency

## The Problem

Files are growing past Claude's efficiency threshold (~800-1000 lines). Current state:

| File | Lines | Status |
|---|---|---|
| Category.lean | 3,126 | **3x over threshold** |
| Algebra.lean | 2,762 | **2.7x over** |
| Applied.lean | 2,618 | **2.6x over** |
| Analysis.lean | 2,217 | **2.2x over** |
| Topology.lean | 1,930 | **1.9x over** |
| RingTheory.lean | 1,434 | **1.4x over** |
| Data.lean | 686 | OK |
| LinearAlgebra.lean | 429 | OK |
| MeasureTheory.lean | 396 | OK |
| Foundation.lean | 332 | OK (stable) |
| Geometry.lean | 155 | OK |

Without splitting, the predicted final sizes are catastrophic:
- Algebra.lean → 11,090 lines
- RingTheory.lean → 9,904 lines
- Analysis.lean → 9,548 lines
- Topology.lean → 9,220 lines

## The Target

**~35 files, each under 800 lines.** Organized by domain folders. Import depth: 3 reads max (Foundation → Domain/Core → Domain/Specific).

## Current Content Map

### Foundation.lean (332 lines) — NO CHANGE
- Val type, mul, add, neg, inv, fdiv, valMap, valPair
- All simp lemmas, sort predicates, injectivity
- valMap_injective/surjective/ext/id/comp
- Sort-predicate interaction, contents_congr/container_congr

### Algebra.lean (2,762 lines) — SPLIT INTO 4 FILES
Current sections with approximate line ranges:
1. **SECTION 1: Lifted Laws** (lines 1-268) — ~268 lines
2. **SECTION 2: Ring and Field Laws** (lines 269-327) — ~59 lines
3. **SECTION 3: Ordered Fields** (lines 328-418) — ~91 lines
4. **SECTION 4: Vector Spaces** (lines 419-532) — ~114 lines
5. **SECTION 5: Polynomial Ring** (lines 533-645) — ~113 lines
6. **SECTION 6: Functional Analysis** (lines 646-733) — ~88 lines
7. **SECTION 7: Spectral Theory** (lines 734-761) — ~28 lines
8. **SECTION 8: Representation Theory** (lines 762-1271) — ~510 lines
9. **SECTION 9: Field Theory** (lines 1272-2297) — ~1,026 lines
10. **SECTION 10: Group Theory** (lines 2298-2762) — ~465 lines

**Split plan:**
| New file | Contains | Est. lines |
|---|---|---|
| `Val/Algebra/Core.lean` | Sections 1-7 (lifted laws, ring/field, ordered, vector, poly, functional, spectral) | ~761 |
| `Val/Algebra/RepTheory.lean` | Section 8 (representation theory) | ~510 |
| `Val/Algebra/FieldTheory.lean` | Section 9 (field theory, Galois) | ~1,026 |
| `Val/Algebra/GroupTheory.lean` | Section 10 (group theory) | ~465 |

**Import chain:** Foundation → Algebra/Core → Algebra/{RepTheory, FieldTheory, GroupTheory}

**Note:** Algebra/Core.lean at 761 is borderline. If it grows during Algebra B3 stair (9,152 B3), it may need further splitting. But for now it holds.

### Category.lean (3,126 lines) — SPLIT INTO 4 FILES
Current sections:
1. **Core** (lines 1-126) — ~126 lines
2. **Monoidal** (lines 127-226) — ~100 lines
3. **Functor** (lines 227-330) — ~104 lines
4. **Limit** (lines 331-405) — ~75 lines
5. **Adjunction** (lines 406-498) — ~93 lines
6. **Preadditive** (lines 499-580) — ~82 lines
7. **Abelian** (lines 581-684) — ~104 lines
8. **Linear** (lines 685-754) — ~70 lines
9. **Enriched** (lines 755-921) — ~167 lines
10. **Condensed** (lines 922-1326) — ~405 lines
11. **Model Theory** (lines 1327-3126) — ~1,800 lines

**Split plan:**
| New file | Contains | Est. lines |
|---|---|---|
| `Val/Category/Core.lean` | Sections 1-9 (core categorical infrastructure) | ~921 |
| `Val/Category/Condensed.lean` | Section 10 (condensed mathematics) | ~405 |
| `Val/Category/ModelTheory.lean` | Section 11 (model theory — all B3 subsections) | ~800 |
| `Val/Category/ModelTheoryB3.lean` | Overflow from ModelTheory if >800 | ~1,000 |

**Import chain:** Foundation → Algebra/Core → Category/Core → Category/{Condensed, ModelTheory}

**Note:** ModelTheory is 1,800 lines — needs splitting into ModelTheory.lean (~800) and ModelTheoryB3.lean (~1,000). Or reorganize by subtopic (Semantics, Satisfiability, Fraisse, etc.).

### Analysis.lean (2,217 lines) — SPLIT INTO 3 FILES
Current sections: 23 numbered sections.

**Split plan:**
| New file | Contains | Est. lines |
|---|---|---|
| `Val/Analysis/Core.lean` | Sections 1-8 (core, special functions, normed, convex, calculus, Fourier, analytic, asymptotics) | ~753 |
| `Val/Analysis/Advanced.lean` | Sections 9-16 (asymptotic limits, box integral, bump, complex, meromorphic, distribution, ODE, polynomial) | ~759 |
| `Val/Analysis/Spaces.lean` | Sections 17-23 (matrix, Lp, functional spaces, real spaces, inner product, C*-algebra, locally convex) | ~705 |

**Import chain:** Foundation → Algebra/Core → Analysis/Core → Analysis/{Advanced, Spaces}

### Topology.lean (1,930 lines) — SPLIT INTO 3 FILES
Current sections: 11 sections.

**Split plan:**
| New file | Contains | Est. lines |
|---|---|---|
| `Val/Topology/Core.lean` | Sections 1-6 (core, connected, continuous, compact, uniform, metric) | ~593 |
| `Val/Topology/Advanced.lean` | Sections 7-10 (algebra, homotopy, sheaf, category sheaf) | ~247 |
| `Val/Topology/Dynamics.lean` | Section 11 (dynamics — all B3 content) | ~1,090 |

**Import chain:** Foundation → Algebra/Core → Topology/Core → Topology/{Advanced, Dynamics}

**Note:** Dynamics at 1,090 is over threshold. May need further split after remaining B3 is written.

### Applied.lean (2,618 lines) — SPLIT INTO 5 FILES
Current content: Probability, HomologicalAlgebra, InformationTheory, SetTheory, Computability, Logic, Combinatorics.

**Split plan:**
| New file | Contains | Est. lines |
|---|---|---|
| `Val/Applied/Probability.lean` | Probability + InformationTheory | ~600 |
| `Val/Applied/HomologicalAlgebra.lean` | Homological algebra (chain complexes, exact sequences) | ~200 |
| `Val/Applied/SetTheory.lean` | Set theory (ordinals, cardinals, ZFC) | ~738 |
| `Val/Applied/Computability.lean` | Computability (automata, Turing, recursive, reducibility) | ~823 |
| `Val/Applied/Logic.lean` | Logic + Combinatorics (to be written in stairs 10-11) | ~200+ |

**Import chain:** Foundation → Algebra/Core → Applied/{each file}

### RingTheory.lean (1,434 lines) — SPLIT INTO 2 FILES
**Split plan:**
| New file | Contains | Est. lines |
|---|---|---|
| `Val/RingTheory/Core.lean` | Current RingTheory content (ideals through schemes) | ~750 |
| `Val/RingTheory/NumberTheory.lean` | Number theory section | ~684 |

**Import chain:** Foundation → Algebra/Core → RingTheory/Core → RingTheory/NumberTheory

### Remaining files — NO CHANGE (under threshold)
| File | Lines | Action |
|---|---|---|
| `Val/MeasureTheory.lean` | 396 | Keep as-is. Will grow to ~800 with B3, still OK. |
| `Val/Data.lean` | 686 | Keep as-is. Will grow to ~800 with B3, still OK. |
| `Val/LinearAlgebra.lean` | 429 | Keep as-is. |
| `Val/Geometry.lean` | 155 | Keep as-is. Will grow to ~600 with B3, still OK. |
| `Val/Foundation.lean` | 332 | Keep as-is. Stable. |

**Note:** MeasureTheory (396 → ~4,106 predicted) and Data (686 → ~4,528 predicted) WILL need splitting when their B3 stairs are reached. But they're fine for now. Split them at stair time when we know the actual content.

## Target File Structure

```
Val/
  Foundation.lean              332   (stable)
  Algebra/
    Core.lean                  761   (lifted laws + ring/field/ordered/vector/poly/functional/spectral)
    RepTheory.lean             510   (representation theory)
    FieldTheory.lean         1,026   (field theory — may split further)
    GroupTheory.lean           465   (group theory)
  Category/
    Core.lean                  921   (functors through enriched)
    Condensed.lean             405   (condensed mathematics)
    ModelTheory.lean           800   (model theory core)
    ModelTheoryB3.lean       1,000   (model theory B3 overflow)
  Analysis/
    Core.lean                  753   (sections 1-8)
    Advanced.lean              759   (sections 9-16)
    Spaces.lean                705   (sections 17-23)
  Topology/
    Core.lean                  593   (sections 1-6)
    Advanced.lean              247   (sections 7-10)
    Dynamics.lean            1,090   (dynamics B3 — may split)
  Applied/
    Probability.lean           600   (probability + information theory)
    HomologicalAlgebra.lean    200   (chain complexes, exact sequences)
    SetTheory.lean             738   (ordinals, cardinals, ZFC)
    Computability.lean         823   (automata, Turing, recursive)
    Logic.lean                 200+  (logic — to be written)
  RingTheory/
    Core.lean                  750   (ideals through schemes)
    NumberTheory.lean          684   (number theory)
  MeasureTheory.lean           396   (will split at stair time)
  LinearAlgebra.lean           429   (stable)
  Data.lean                    686   (will split at stair time)
  Geometry.lean                155   (will split at stair time)
```

**Total: ~31 files. Largest: ~1,090 (Dynamics). Most: 400-800 range.**

## Import Chain

```
Foundation.lean (root — imports nothing)
  ├── Algebra/Core.lean (imports Foundation)
  │   ├── Algebra/RepTheory.lean
  │   ├── Algebra/FieldTheory.lean
  │   ├── Algebra/GroupTheory.lean
  │   ├── Category/Core.lean
  │   │   ├── Category/Condensed.lean
  │   │   ├── Category/ModelTheory.lean
  │   │   └── Category/ModelTheoryB3.lean
  │   ├── Analysis/Core.lean
  │   │   ├── Analysis/Advanced.lean
  │   │   └── Analysis/Spaces.lean
  │   ├── Topology/Core.lean
  │   │   ├── Topology/Advanced.lean
  │   │   └── Topology/Dynamics.lean
  │   ├── Applied/Probability.lean
  │   ├── Applied/HomologicalAlgebra.lean
  │   ├── Applied/SetTheory.lean
  │   ├── Applied/Computability.lean
  │   ├── Applied/Logic.lean
  │   ├── RingTheory/Core.lean
  │   │   └── RingTheory/NumberTheory.lean
  │   ├── MeasureTheory.lean
  │   ├── LinearAlgebra.lean
  │   ├── Data.lean
  │   └── Geometry.lean
```

**Max depth: 3 reads** (Foundation → Domain/Core → Domain/Specific).
**No circular dependencies.**

## Cross-Domain Imports

Some files currently have cross-domain imports:
- Topology imports Analysis (for `liftConv`) and Category (for `valMap_unique`, `valJoin`)
- Applied imports Analysis, MeasureTheory, Category, RingTheory
- Geometry imports Analysis, Category, RingTheory

After split, these become:
- `Topology/Core.lean` imports `Analysis/Core.lean` + `Category/Core.lean`
- `Applied/Probability.lean` imports `Analysis/Core.lean` + `MeasureTheory.lean`
- `Applied/SetTheory.lean` imports `Algebra/Core.lean` only
- `Applied/Computability.lean` imports `Algebra/Core.lean` only
- `Geometry.lean` imports `Analysis/Core.lean` + `Category/Core.lean` + `RingTheory/Core.lean`

No circular dependencies. Each cross-domain import is to a Core file, never to a specific subdomain file.

## Execution Plan

**Phase 1: Create folder structure**
```bash
mkdir -p Val/Algebra Val/Category Val/Analysis Val/Topology Val/Applied Val/RingTheory
```

**Phase 2: Split files (one at a time, build after each)**
1. Split Algebra.lean → 4 files. Build.
2. Split Category.lean → 4 files. Build.
3. Split Analysis.lean → 3 files. Build.
4. Split Topology.lean → 3 files. Build.
5. Split Applied.lean → 5 files. Build.
6. Split RingTheory.lean → 2 files. Build.

**Phase 3: Delete old files, full build**
- Remove old monolithic files
- `lake build` all modules
- `./scripts/audit.sh`

**Phase 4: Update audit script**
- Update glob patterns from `Val/*.lean` to `Val/**/*.lean`
- Verify audit still catches all duplicate patterns

**Phase 5: Update documentation**
- CLAUDE.md file structure section
- README.md file listing
- PROGRESSION_STEP5.md remaining stairs map

## How Remaining Stairs Map to New Files

| Stair | Domain | Target file |
|---|---|---|
| 9 | GroupTheory | Val/Algebra/GroupTheory.lean |
| 10 | Combinatorics | Val/Applied/Combinatorics.lean (new) |
| 11 | NumberTheory | Val/RingTheory/NumberTheory.lean |
| 12 | RingTheory+LinAlg | Val/RingTheory/Core.lean + Val/LinearAlgebra.lean |
| 13 | CategoryTheory+AlgTop | Val/Category/Core.lean (may split further) |
| 14 | Geometry+AlgGeom | Val/Geometry.lean (will split to folder) |
| 15 | MeasureTheory+Prob | Val/MeasureTheory.lean (will split to folder) |
| 16 | Data | Val/Data.lean (will split to folder) |
| 17 | Topology+Order | Val/Topology/Core.lean + Val/Topology/Order.lean (new) |
| 18 | Analysis | Val/Analysis/{Core,Advanced,Spaces}.lean |
| 19 | Algebra | Val/Algebra/Core.lean (may split further) |

Files that will need further splitting at stair time:
- MeasureTheory.lean → folder when stair 15 adds ~4,000 B3 lines
- Data.lean → folder when stair 16 adds ~4,000 B3 lines
- Geometry.lean → folder when stair 14 adds ~3,500 B3 lines

## The Principle

Every file under 800 lines. Every domain reachable in 3 reads. No circular dependencies. Split when it hurts, not before. The files serve the AI, not the human.
