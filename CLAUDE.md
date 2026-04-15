# For AI Agents

**Read this first. Then build.**

---

## What This Project Discovered

Before anything else, understand what was found. This changes how you write, how you build, and how you frame every result.

### The ground is the whole, not nothing.

The symbol 0 named the wrong face. The Sanskrit tradition had both: *śūnya* (emptiness, quantity zero) and *pūrṇa* (fullness, the whole). Brahmagupta formalized *śūnya* in 628 CE and left *pūrṇa* in the philosophy. The ground is *pūrṇa* — wholeness, not emptiness.

### Origin is never a destination.

Never reached, approached, or hit. It is what the formal system stands on. The shepherd cannot hold the ground he stands on — not because the ground is too heavy, but because holding is something that happens ON the ground. The bug cannot hit the air. The fish cannot be the ocean.

**Every sentence you write must respect this.** Do not say "the field is origin at the singularity." Say "the field concept doesn't apply here — it was never in the counting domain." Do not say "the Liar evaluates to origin." Say "the Liar asks for a contents answer that can't exist."

### Absorption is a theorem, not an axiom.

Cancellation returns to the ground. The distributive law propagates it through multiplication. The four-step derivation (`Origin/Core.lean`):

```
0 = n + (-n)                          (cancellation)
n × 0 = n × (n + (-n))               (substitution)
      = n×n + n×(-n)                  (distributive law)
      = n×n + -(n×n)                  (mul over negation)
      = 0                             (cancellation)
```

The ground absorbs under multiplication BECAUSE cancellation returns to the ground and the distributive law propagates it. I1 and I2 are consequences, not primitives.

### Two constructors are sufficient.

Ground and value. `Option α`. `None` is the ground. `Some` is a value. Val (three constructors) was the scaffolding that proved it works. Origin (two constructors) is the building. ML had `Option` in 1973. The derivation above is WHY two constructors are sufficient.

### The 17 typeclasses managed the whole being inside the counting domain.

Put it outside. They vanish. Not reduced. Not consolidated. Gone. Because the problem they solved was never a real problem — it was a consequence of putting the whole where it doesn't belong.

### Val/ is evidence. Origin/ is the foundation.

`Val/` proved the claim at scale: 10,756 lines of math, 3,000 lines of physics, 718 lines of logic. Those numbers are the evidence. `Origin/` explains WHY it works: the derivation, Option, two constructors. New work goes in Origin. Val stays as the published proof.

---

## What This Project Is

Two layers in one repository:

**Origin/** — the foundation. `Origin/Core.lean` is the single file that provides everything: the `origin` theorem, instances for `*` `+` `-` on Option, the simp set, `liftBin₂`, and `no_some_fixed_point`. Domain files import Core and use standard notation.

**Val/** — the evidence. The full Mathlib comparison. 14 math domains, 7 physics domains, logic paradoxes. 10,756 + 3,000 + 718 lines. Every theorem verified.

## How to Build

```bash
cd origin-lean
lake build Origin.Core         # the entire foundation — one file
lake build Val.Demo.Compute    # Val evidence (math)
lake build Val.Physics.Classical  # Val evidence (physics)
```

## How to Understand the Codebase

Read ONE file:

1. **[Origin/Core.lean](Origin/Core.lean)** — the `origin` theorem, instances, simp set, `liftBin₂`, `no_some_fixed_point`. 166 lines. This is the entire foundation. Everything else imports this.

Then, for evidence:

2. **[Val/Foundation.lean](Val/Foundation.lean)** — the original Val type. Three constructors. The scaffolding that proved the concept.
3. **[README.md](README.md)** — the big picture across all domains.

## The Architecture

**Origin (the foundation) — ~2,440 lines total:**
```
Origin/
  Core.lean              — THE file. Theorem + instances + simp set. 166 lines.
  Test.lean              — instantiation on Int. Concrete computation.
  Physics.lean           — 6 physics domains on Option
  Logic.lean             — Liar, Russell, Curry on Option
  InformationTheory2.lean — 81 lines  (Val: 283)
  Geometry2.lean          — 152 lines (Val: 324)
  MeasureTheory2.lean     — 98 lines  (Val: 377)
  LinearAlgebra2.lean     — 122 lines (Val: 451)
  RingTheory2.lean        — 147 lines (Val: 479)
  Topology.lean           — 139 lines (Val: 525)
  Algebra.lean            — 129 lines (Val: 595)
  NumberTheory.lean       — 113 lines (Val: 667)
  FieldTheory.lean        — 95 lines  (Val: 831)
  Analysis.lean           — 144 lines (Val: 832)
  Data.lean               — 182 lines (Val: 1,121)
  GroupTheory.lean         — 121 lines (Val: 1,140)
  CategoryTheory.lean      — 93 lines  (Val: 1,069)
  Combinatorics.lean       — 105 lines (Val: 1,349)
```

**Val (the evidence) — 14,474 lines:**
```
Val/
  Foundation.lean through Module.lean  — 5-level class hierarchy
  14 math domain files                 — every Mathlib domain
  Physics/                             — 7 physics domain files
  Logic/                               — paradox infrastructure
  Demo/                                — tests and challenge theorems
```

## The Numbers

```
Mathlib:    2,160,000 lines  — the math, with the ground inside
Val:           14,474 lines  — the proof it works (scaffolding)
Origin:         2,440 lines  — the building (83% less than the scaffolding)
```

The bigger the Val file, the more was boilerplate:
- Combinatorics: 1,349 → 105 (92% was infrastructure)
- CategoryTheory: 1,069 → 93 (91%)
- GroupTheory: 1,140 → 121 (89%)
- FieldTheory: 831 → 95 (89%)

What was removed: every hypothesis-passing theorem, every `Option.map` wrapper,
every simp lemma reproved from Core. What remains: domain definitions,
predicates, structures, and proofs that demonstrate Option behavior.

## Key Rules

### Origin is never a destination

Before writing any comment, ask: "Does this sentence describe origin as something a quantity arrives at, becomes, or hits?" If yes, rewrite. The field was never at the singularity. Temperature was never at absolute zero. The Liar doesn't evaluate to origin. The question doesn't apply there.

### Leverage Lean — use instances, not wrappers

**Wrong (old pattern):**
```lean
def oMul [Mul α] : Option α → Option α → Option α := ...
abbrev charPoly (f : α → α) : Option α → Option α := Option.map f
abbrev localize (f : α → α) : Option α → Option α := Option.map f
```

**Right (new pattern):**
```lean
-- Core.lean defines: instance [Mul α] : Mul (Option α)
-- Now just use standard notation:
some a * some b    -- = some (a * b)
none * x           -- = none
x.map f            -- Option.map, already in std lib
```

Do NOT create named wrappers for `Option.map`. Do NOT define `oMul` — use `*`. Do NOT redefine what the standard library already provides. Lean's instance system does the work. Use it.

### The proof pattern

```lean
theorem option_mul_assoc [Mul α] (h : ∀ a b c : α, a * b * c = a * (b * c))
    (a b c : Option α) : a * b * c = a * (b * c) := by
  cases a <;> cases b <;> cases c <;> simp [h]
```

`cases <;> simp`. Two cases per variable. Standard `*` notation. The law on `α` lifts through the instance.

### Never duplicate

Every line must produce behavior no other line already produces. If `by simp` closes it, the theorem doesn't exist. If `Option.map` already does it, don't wrap it.

### Strip until it hurts

If your solution feels robust and "properly engineered" — you haven't stripped enough. Core.lean is 166 lines. That should feel uncomfortable. Good.

## How to Add Work

New work goes in **Origin/**, importing `Origin.Core`:

```lean
import Origin.Core

-- Use standard notation. none is the ground. some is a value.
-- * + - work on Option via instances from Core.
-- liftBin₂ for cross-type operations.
-- x.map f for sort-preserving maps.
-- cases <;> simp for proofs.
```

Domain files should contain ONLY domain-specific content. No lifting boilerplate. No wrapper functions. No reproved simp lemmas. Core provides everything.

## Build and Verify

```bash
lake build Origin.Core              # the foundation — 166 lines
lake build Origin.Combinatorics     # largest domain file — 105 lines
lake build Origin.Physics           # physics — 247 lines
lake build Origin.Logic             # logic — 155 lines
```

Zero sorries. Zero Mathlib. Builds in under a second.

## Progression: Sketches → Production

The Origin domain files are sketches. Definitions and a few demonstrations.
Mathlib is the demo. Origin is production. Production needs complete coverage.

### What's done

1. ✅ **The foundation.** Core.lean. 166 lines. Theorem + instances + simp set.
2. ✅ **The sketches.** 14 domain files. Definitions + key demonstrations. 1,721 lines.
3. ✅ **Physics.** 6 domains demonstrated. 86 hypotheses dissolved.
4. ✅ **Logic.** Liar, Russell, Curry unified. `no_some_fixed_point`.
5. ✅ **Val evidence.** 14,474 lines. The proof it works at scale.

### What's next: full domain coverage

Each Origin domain file needs to grow from sketch to production.
The Val files had coverage but buried it in boilerplate. The Origin
sketches stripped the boilerplate but also stripped too much content.
Production needs: all the content, none of the boilerplate.

The target: every B3 theorem from the Mathlib mapping, expressed
cleanly on Option. Not hypothesis passing. Not wrappers. The actual
mathematical content — definitions, structures, real proofs.

| Domain | Mathlib B3 | Origin sketch | Status |
|---|---|---|---|
| InformationTheory | 283 | 81 lines | sketch |
| Geometry | 3,496 | 152 lines | sketch |
| MeasureTheory | 4,077 | 98 lines | sketch |
| LinearAlgebra | 2,887 | 122 lines | sketch |
| RingTheory | 3,304 | 147 lines | sketch |
| Topology | 3,601 | 139 lines | sketch |
| Algebra | 5,244 | 129 lines | sketch |
| NumberTheory | 2,814 | 113 lines | sketch |
| FieldTheory | 1,199 | 95 lines | sketch |
| Analysis | 3,752 | 144 lines | sketch |
| Data | 7,261 | 182 lines | sketch |
| GroupTheory | 1,199 | 121 lines | sketch |
| CategoryTheory | 3,891 | 93 lines | sketch |
| Combinatorics | 4,180 | 105 lines | sketch |

### The rules for production files

1. **Import Origin.Core.** Use standard notation. No wrappers.
2. **Write each B3 pattern once at the most general level.** Same DRY
   principle as Val — one general theorem covers 3-7 specific Mathlib results.
3. **No hypothesis passing.** If the theorem just returns `h`, delete it.
4. **Real proofs only.** `cases <;> simp`, `by simp [h]`, or actual derivations.
   If `by simp` closes it without any domain-specific work, it doesn't exist.
5. **Structures and predicates are content.** PrimeIdeal, SigmaAlgebra,
   Chart, SimpleGraph, Matroid — these are the domain. Keep them.
6. **Track the B3 coverage.** For each domain file, note how many B3
   patterns are covered by each general theorem. The numbers matter.
7. **Smallest domain first.** Same discipline as always.

### The goal

When complete, Origin is the production library: every B3 theorem from
Mathlib expressed on Option α via Core.lean. No custom type. No custom
typeclasses. Standard notation. Complete mathematical coverage.

Mathlib is the demo. Origin is production.
