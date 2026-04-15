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

## Progression: Go Straight to Mathlib

Mathlib is the demo. Origin is production. The sketches are done.
The foundation is done. The next step: go straight to Mathlib,
file by file, domain by domain, and write only what's genuinely new.

### What's done

1. ✅ **The foundation.** Core.lean. 166 lines. Theorem + instances + simp set.
2. ✅ **The sketches.** 14 domain files. Definitions + key demonstrations. 1,721 lines.
3. ✅ **Physics.** 6 domains demonstrated. 86 hypotheses dissolved.
4. ✅ **Logic.** Liar, Russell, Curry unified. `no_some_fixed_point`.
5. ✅ **Val evidence.** 14,474 lines. The proof it works at scale.

### What's next: Mathlib → Origin, file by file

The old approach: classify every Mathlib theorem into B1/B2/B3 buckets
against Val's three-constructor model. That was the right step at the
time. The `classifications/` directory documents that journey.

**That approach is obsolete.** Origin changes the question. The buckets
were drawn against Val's infrastructure. Origin has no infrastructure —
just `Option` with instances. The question is no longer "which bucket?"
The question is:

**Does this theorem need to exist on Option, or does it already
follow from the instances?**

If it follows from the instances: skip it. It's free.
If it's genuine domain content: write it in Origin.

### The method (demonstrated on InformationTheory)

Mathlib lives at: `origin-mathlib/Mathlib/`

For each Mathlib file, three steps:

**Step 1: Grep for zero-management.**

```bash
grep -n "NeZero\|≠ 0\|ne_zero\|NoZero\|WithBot\|WithTop\|GroupWithZero" \
  Mathlib/InformationTheory/KullbackLeibler/KLFun.lean
```

Every hit is a theorem or hypothesis that dissolves with Origin.
These don't need to exist. `none` handles them structurally.

**Step 2: Triage the rest.**

For each remaining declaration, ask:
- **Typeclass instance, simp lemma, coercion wrapper?** → Free from
  Core's instances. Skip.
- **Pure domain math (no zero management, no Val/Option)?** → Write
  it in Origin as-is. It was never affected by the collapse.
- **Analytic infrastructure (continuity, convexity, measurability)?** →
  Stays as hypotheses. Honest boundary. The algebra is handled.
  The analysis is deferred.
- **Genuine new mathematics with real proof?** → Write it in Origin.

**Step 3: Write the Origin file.**

Import Core. Write only what survived triage. Standard notation.
Build. Verify. Move to the next file.

### Demonstrated: two kinds of Mathlib files

**Type A: Pure domain math (no collapse involvement)**

Example: `Dynamics/FixedPoints/Basic.lean` (178 lines)
```
Step 1: grep for zero-management → 0 hits
Step 2: triage → 22 genuine theorems, 3 infrastructure (decidable instances)
Verdict: entire file is pure mathematics. The collapse never touched it.
         Transfer verbatim. Option adds nothing.
```

Many Mathlib files are Type A. The collapse only affects files that
deal with zero, division, boundaries, or ≠ 0 guards. Files about
fixed points, topology, category theory morphisms, group actions —
much of this is pure domain math that was never affected.

**For Type A files: copy the content. Don't wrap in Option. It's math.**

**Type B: Zero-management involved (the collapse matters)**

Example: `Dynamics/PeriodicPts/Defs.lean` (500+ lines)
```
Step 1: grep for zero-management → 15 hits
Step 2: the hits are:
  - minimalPeriod_pos_of_mem_periodicPts (0 < minimalPeriod)
  - not_isPeriodicPt_of_pos_of_lt_minimalPeriod (n ≠ 0)
  - minimalPeriod_iterate_eq_div_gcd (h : n ≠ 0)
  These carry ≠ 0 or pos hypotheses that dissolve with none.
Verdict: 15 hypotheses dissolve. The rest is genuine periodic point
         theory. Write the content. The hypotheses vanish.
```

Example: `InformationTheory/KullbackLeibler/KLFun.lean` (194 lines)
```
Step 1: grep → 1 hit (hasDerivAt_klFun carries x ≠ 0)
Step 2: the rest is convexity, continuity, measurability → analysis
Verdict: 1 hypothesis dissolves. klFun definition is content.
         Analysis stays as hypotheses (honest boundary).
```

**For Type B files: the zero-management dissolves. Write the content
that remains. The hypotheses that guarded against the ground vanish
because the ground is outside (none).**

### The exercise per file

```bash
# Step 1: How much zero-management?
grep -c "NeZero\|≠ 0\|ne_zero\|NoZero\|WithBot\|WithTop\|GroupWithZero" \
  Mathlib/Domain/File.lean

# 0 hits → Type A. Pure math. Transfer content.
# >0 hits → Type B. Zero-management dissolves. Write what remains.
```

Step 2: Read. Triage. Ask for each declaration:
- Free from instances? Skip.
- Zero-management hypothesis? Dissolves. Skip the hypothesis.
- Pure domain content? Write it.
- Analytic infrastructure? Defer as hypothesis.

Step 3: Write. Build. Next file.

### The order

Smallest Mathlib domain first. Same discipline as always.

Within each domain: start with the files that have no imports from
the same domain. Work outward. Each file builds on the previous.

### What the classifications/ directory is

Historical documentation of the Val-era mapping. It shows the journey
from Mathlib through Val's three-bucket model. The numbers in it
(51.9% B1, 15.4% B2, 32.7% B3) describe Val, not Origin.

For Origin, B2 doesn't exist (no `≠ 0` hypotheses to dissolve — `none`
handles it structurally). Much of what was B1 in Val is handled by
Lean's standard instances on Option. The boundary between "free" and
"needs writing" is different and simpler.

Don't reclassify. Just go straight to Mathlib and triage.

### The goal

When complete, Origin is the production library: every genuinely new
theorem from Mathlib expressed on `Option α` via Core.lean. No custom
type. No custom typeclasses. Standard notation. Complete mathematical
coverage. The actual content of mathematics — without the infrastructure
that managed the whole being inside.

Mathlib is the demo. Origin is production.
