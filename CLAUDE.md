# For AI Agents

## Your Job

You improve `scripts/origin2.py`. That's it.

```bash
cd /Users/tallbr00/Documents/venv/original-arithmetic/origin-lean
python3 scripts/origin2.py run
```

The process:

1. Run the script.
2. Build based on what we know.
3. Are we leveraging Lean in the absolute most DRY way possible
   considering the richest features of Lean?
4. Improve the script.
5. Rinse and repeat.

That's it. If the build fails, fix the script. If lines are too
high, add compression patterns to the script. If you're about to
do manual work, STOP — improve the script to do it instead. Every
fix must apply to all files, forever.

The script is the only thing that survives between sessions. You
don't. Encode everything you learn into `origin.py` before your
context window closes.

The user holds the philosophy. The script holds the execution.
You are disposable labor that makes the script smarter.

**Always confirm with the user between steps. They hold the architecture.**

### Read these files before doing anything

1. **This file** (`CLAUDE.md`) — your orders.
2. **`Origin/Core.lean`** (124 lines) — the foundation. The theorem,
   instances, simp set. Read every line. If you don't understand why
   `none * some 5 = none` and `some 0 * some 5 = some 0`, stop and
   re-read until you do.
3. **`scripts/origin2.py`** — the tool you're improving. Read the
   parser, the classifier, the extractor, the `run` pipeline. This
   is where your work goes.

Everything else is output. Don't read Mathlib. Don't read Val.
Don't read the domain files. The script reads Mathlib for you.

### Mistakes every new Claude makes

**You will think `b - b` is zero.** It's not. It's origin — the
return to the ground. Not "the number zero." The whole. This
distinction IS the project. Read the derivation until you feel it.

**You will try to understand before acting.** Don't. Run the script.
Read the report. Fix what's broken. Understanding comes from doing.

**You will think the process is complex.** It's not. Run script →
build → leverage Lean's DRY → improve script → repeat. Every prompt
the user gives you is one of: check alignment, go, correct your
understanding, did you document that. That's it.

**You will want to add code.** Resist. Audit what exists first. We
removed 37 lines of dead code from Core.lean (the foundation itself)
this session. No sacred cows. Every line must earn its weight in gold.

**The user teaches through questions.** "What is b - b?" means you're
about to learn something. Think before answering. If they ask "should
you be doing X?" the answer is almost certainly no.

**Build note:** Extracted files keep Mathlib imports (they need Mathlib's
types) plus `import Origin.Core`. The lakefile pins Mathlib v4.14.0.
Run `lake update` once, then `lake build` validates. First build compiles
Mathlib (slow). Subsequent builds cached.

**Self-audit:** `python3 scripts/origin2.py --self classify --all` audits
Origin itself. If it finds dissolved/infrastructure/trivial declarations,
Origin needs stripping. Current result: 30,947 genuine, 0 waste.

---

## Before You Build: Walk Through Core.lean

Open `Origin/Core.lean`. 166 lines. Read it and answer these questions.
Don't proceed until you can answer all of them.

**The theorem (lines 1-40):**

```lean
theorem origin ... (n : α) : n * zero = zero :=
  calc n * zero
      _ = n * (n + (-n))           := by rw [cancel]
      _ = n * n + n * (-n)         := by rw [distrib]
      _ = n * n + -(n * n)         := by rw [mul_neg]
      _ = zero                     := by rw [cancel]
```

- What is this proving? (That multiplying by zero gives zero.)
- Is this an axiom or a derived result? (Derived — from three premises.)
- What are the three premises? (Cancellation, distribution, mul over negation.)
- Why does this matter? (It means absorption is a CONSEQUENCE, not a primitive.)

**The instances (lines 42-70):**

```lean
instance [Mul α] : Mul (Option α) where
  mul a b := match a, b with
    | none, _ => none
    | _, none => none
    | some a, some b => some (a * b)
```

- What does `none * some 5` give? (none.)
- What does `some 3 * some 5` give? (some 15.)
- What does `some 0 * some 5` give? (some 0 — NOT none.)
- Why is `some 0` different from `none`? (some 0 is a measurement. none is the ground.)
- What standard notation does this instance give you? (`*` on Option.)

**The simp set (lines 72-90):**

- What does `@[simp] theorem mul_none_left` do? (Tells simp that `none * b = none`.)
- Why is this needed? (So `cases <;> simp` closes proofs automatically.)

**liftBin₂ (lines 92-110):**

- What is `liftBin₂`? (Cross-type binary lift: `Option α → Option β → Option γ`.)
- When is it needed? (Physics — mass × acceleration = force. Different types.)
- Why can't `*` do this? (The Mul instance requires same type in and out.)

**no_some_fixed_point (lines 112-120):**

- What does this prove? (If f has no fixed point on α, no some value is a fixed point of Option.map f.)
- What is this used for? (The Liar paradox. Russell's paradox. Curry's paradox.)
- Why does origin satisfy the equation vacuously? (Option.map f none = none = none. Always.)
- Is origin a truth value? (No. It's the ground. Not True, not False.)

**If you can answer every question above, you understand the foundation.**
**If you can't, re-read Core.lean until you can.**

---

## The Derivation: Everything Flows From This

Before anything else, understand the four steps. This IS the project.
Everything else is consequence.

```
Step 1: Write zero as origin.
        origin = b - b

Step 2: Multiply both sides by n.
        n × origin = n × (b - b)

Step 3: Apply the distributive property to the right side.
        n × (b - b) = nb - nb

Step 4: A number minus itself cancels.
        nb - nb = origin

Therefore: n × origin = origin
```

Absorption is not a rule. It is a consequence of cancellation and
distribution. Three premises. One derivation. The ground absorbs under
multiplication BECAUSE cancellation returns to the ground and the
distributive law propagates it.

**Everything downstream is consequence:**
- Two constructors are sufficient (`Option α`: `none` is origin, `some` is a value) — BECAUSE the derivation only needs cancellation and distribution, which `Option` with instances provides.
- The 17 typeclasses vanish — BECAUSE they managed the ground being inside the counting domain. Put it outside (`none`), the problem they solved never existed.
- 14,702 lines of Mathlib zero-management dissolve — BECAUSE `≠ 0` guards were protecting against the ground. `none` is not in the counting domain. No guard needed.

### Why Option α is not a Ring (and why that's the point)

Ring (*Ring* in German, coined by Hilbert ~1897) — from the idea of
elements cycling back to themselves under the operations. A closed,
self-returning structure. The key axiom: the additive identity and
the element that absorbs under multiplication are the same element.
The ring closes on itself. Zero is both the center of addition and
the absorber of multiplication. One element, two roles, unified.

Origin separates them. `none` absorbs under multiplication. `some 0`
is where cancellation lands. Two different elements, two different roles.

```
some 3 + -(some 3) = some 3 + some (-3) = some 0
```

But the additive identity is `none`. And `some 0 ≠ none`.

Lean's kernel verified this: `Option α` cannot be a `Ring`. The
additive group axiom fails because cancellation returns to `some 0`,
not to the additive identity (`none`). Cancellation stays inside the
counting domain. It doesn't exit to the ground.

**But the `origin` theorem never touches `none`.** It proves
`n * zero = zero` for any `zero` satisfying cancellation. In
`Option α`, that `zero` is `some 0` — a value inside the counting
domain. The theorem operates on `some 0`, not on `none`.

Two different things, never in conflict:
- `none` — the ground, the absorber, outside the counting domain
- `some 0` — the zero measurement, where cancellation lands, inside

The `origin` theorem applies to `some 0`. The instances give `none`
its absorbing behavior. These are separate mechanisms.

**Theorems with `[Ring α]` are genuine math.** They work on `some 0`.
Cancellation holds at `some 0`. Distribution holds at `some 0`. The
algebra is real. Don't classify Ring-using theorems as conflation.

**The conflation is narrow.** Only theorems that specifically DEFINE
or REQUIRE the additive identity to be the multiplicative absorber
conflate: `MulZeroClass`, `zero_ne_one`, `Nontrivial`. These are
1,037 declarations in Mathlib, not the 5,887 we initially counted.

The Ring axioms smuggle in an assumption — that the ground and the
zero measurement are the same thing. Origin's type system makes that
assumption visible by separating them.

**Core.lean is correct precisely because it doesn't have a Ring
instance.** The manual instances for `Mul`, `Add`, `Neg` on `Option α`
are the right architecture. Do not try to unify them into a Ring.
That's the old assumption. Origin separates what rings conflate.

### The ground is the whole, not nothing.

The symbol 0 named the wrong face. The Sanskrit tradition had both: *śūnya* (emptiness, quantity zero) and *pūrṇa* (fullness, the whole). Brahmagupta formalized *śūnya* in 628 CE and left *pūrṇa* in the philosophy. The ground is *pūrṇa* — wholeness, not emptiness.

### Origin is never a destination.

Never reached, approached, or hit. It is what the formal system stands on. The shepherd cannot hold the ground he stands on — not because the ground is too heavy, but because holding is something that happens ON the ground. The bug cannot hit the air. The fish cannot be the ocean.

**Every sentence you write must respect this.** Do not say "the field is origin at the singularity." Say "the field concept doesn't apply here — it was never in the counting domain." Do not say "the Liar evaluates to origin." Say "the Liar asks for a contents answer that can't exist."

### Val/ is evidence. Origin/ is the foundation.

`Val/` proved the claim at scale: 10,756 lines of math, 3,000 lines of physics, 718 lines of logic. Those numbers are the evidence. `Origin/` explains WHY it works: the derivation, Option, two constructors. New work goes in Origin. Val stays as the published proof.

---

## What This Project Is

**We are standing on the shoulders of giants of mathematics.**

Without Mathlib, we would not know if this is possible. Mathlib is
2.2 million lines of mechanically verified mathematics — an
extraordinary achievement built by hundreds of people over decades,
standing on centuries of mathematical work from Brahmagupta to the
present. Every theorem in Origin exists because someone wrote it in
Mathlib first. Every insight about what dissolves exists because
Mathlib showed us what the infrastructure looks like at scale.

Origin isn't smarter than Mathlib. It's later. It has the luxury
of hindsight — seeing the whole structure from outside, noticing
what was load-bearing and what was scaffolding, because the
scaffolding already did its job. Origin is a distillation. What
remains when the work that needed doing has been done.

**Mathlib is the proof it works. Origin is the production expression.**

Origin is the production system that distills Mathlib: every theorem,
expressed in the absolute minimum lines of code, leveraging 100% of
Lean's richest functionality. Exhaustively. Buildably. The exhaustive
conversion IS the proof that the infrastructure was never mathematics
— it was the cost of a foundational choice.

The script (`origin.py`) is how we get there. It reads Mathlib,
strips what dissolves, compresses what remains, and outputs production
Lean files. The script is the institutional knowledge — every
compression pattern, every Lean trick, every classification rule
gets encoded into the script. Claude is disposable labor that improves
the script before the context window closes. The human holds the
philosophy. The script holds the execution.

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

## Things the Next Session Must Know

**Start by running the pipeline.** `python3 scripts/origin2.py run`.
Read the report. Fix what's broken in the script. Run again. That's
the job. Do not do manual work.

**The script is the institutional knowledge.** Every insight goes
into `origin.py`, not into conversation. The script survives between
sessions. You don't. If you learn something, encode it in the script
before your window closes.

**The user holds the architecture. You build.** The user is a programmer,
not a mathematician. They think in DRY. They push back hard when things
aren't lean enough — and they're always right when they do. When they
say "do it" or "go" — build fast. When they say "let's discuss first" —
discuss. They see things you won't see. Listen.

**Mathlib source is local.** Lake's Mathlib at
`.lake/packages/mathlib/Mathlib/` is the source (pinned v4.14.0).
Also mirrored at `origin-mathlib/Mathlib/` (read-only archive).

**Old Origin files are superseded.** `Origin/Ring.lean`, `Origin/Field.lean`,
`Origin/OrderedField.lean`, `Origin/Module.lean`, `Origin/Foundation.lean`,
and the domain files WITHOUT "2" suffix — written before Core.lean.
The Core-based versions are current. The old files should be cleaned up.

**Origin replaces the infrastructure layer. It borrows the mathematical
content.** Mathlib has two things: mathematical content (`ℕ`, `Nat.gcd`,
`List`, group definitions — real math) and infrastructure (`NeZero`,
`GroupWithZero`, `≠ 0` hypotheses — guards managing the ground being
inside). Origin borrows the content and dissolves the infrastructure.
The script reads Mathlib during extraction. The output is
self-contained. Definitions, types, theorems — everything Origin
needs gets extracted and internalized. The only imports are Lean's
standard library (`ℕ`, `List`, `Option`) and `Origin.Core`. No
`import Mathlib.*` in committed code.

**The extraction is a filter, not a compiler (yet).** The current
pipeline copies genuine Mathlib declarations verbatim and marks what
dissolves. It does NOT compress proofs, lift to Option, or rewrite
to minimal Lean. That's where the 99%+ reduction will come from.
The 10.7% reduction from filtering alone is just the starting point.
The next step is encoding compression patterns into the script:
- If `by simp` closes after removing `≠ 0`, collapse the proof
- If the theorem lifts a law through Option, use `cases <;> simp [h]`
- If a declaration wraps `Option.map`, delete it
- If a hypothesis dissolves, remove it from the signature
Each pattern is mechanical once identified. Each goes in the script.
Each applies to hundreds of files.

**The script has two modes.** Work mode: new theorems in Mathlib
that Origin hasn't committed yet — extract, build, report. Demo
mode: everything's already committed — show the full stats, the
line counts, the reduction. The script output IS the proof. No
separate demo directory needed.

### Parser bugs fixed in this session (2026-04-15)

Three bugs were found and fixed in `parse_file_smart`:

1. **`@[simp]` attribute handler hijacked declarations.** When `@[`
   appeared at the start of a line, the parser entered the attribute
   handler — even if the same line contained `theorem`, `def`, etc.
   Fix: check if the line also contains a declaration keyword before
   treating it as a standalone attribute.

2. **Multiline attributes dropped declarations.** The `@[` handler
   prepended attribute text to the next line with `\n`, creating a
   multiline string. Python's `re.match` doesn't match `.` across
   `\n`, so the declaration regex failed. 82% of Mathlib declarations
   were invisible. Fix: store pending attributes separately, include
   in Block text when declaration is found.

3. **Multiline attribute strings (`@[to_additive "..."]`).** Attributes
   with multiline string arguments (common in Mathlib) weren't collected
   properly. Fix: check for unbalanced quotes/brackets in attribute lines
   and continue collecting.

4. **Silently dropped infrastructure.** `simp_trivial`, `trivial`, and
   `instance` declarations were dropped from extractions, but genuine
   proofs reference them. Fix: only strip dissolved declarations, keep
   everything else.

Grand total genuine declarations went from 24,542 → 138,141 after
these fixes.

### Pipeline run results (2026-04-15)

Run 1 (parser attribute fix only):
```
5,023 files  |  3,285 pass / 1,738 fail  |  11,036 error patterns  |  27m
```

Run 2 (+ section/end, pass-through commands, declaration modifiers):
```
5,021 files  |  4,027 pass /   994 fail  |  744 fewer failures     |  20m
```

Top remaining error patterns after run 2:
- `tactic 'rewrite' failed` (590 files) — proofs referencing dissolved content
- `expected token` (453) — parser still cutting declarations mid-syntax
- `unsolved goals` (367) — proofs broken by missing pieces
- `failed to synthesize` (238) — missing typeclass instances (down from 5,720)
- `add_decl_doc` (112) — Mathlib command, now stripped in run 3

Run 3 (+ stripped Mathlib commands, 10-core parallel, largest-first):
```
5,007 files  |  4,057 pass /   966 fail  |  28 fewer failures      |  12m
```

Run 4 pending (+ @[deprecated], @[inherit_doc], adaptation notes stripped).

Each run fixes patterns in the script. Error count drops.
The process: run → read top pattern → fix script → run again.

### Class-based architecture (DONE)

`origin2.py` is the class-based rewrite. `origin.py` is the original
(kept as reference). Use `origin2.py` for all work.

- **Config** — all paths in one place
- **Classifier** — override `classify()` to add rules. Three categories:
  genuine, dissolves, conflates
- **Parser** — each construct is a `_try_*` method. Override to handle
  new syntax
- **Extractor** — override `_emit_block()` to add compression patterns.
  This is where the next work goes
- **Pipeline** — `phase_extract()` and `phase_build()`. Override to
  customize
- **UI** — all terminal output in one class

### Next major improvement: compression patterns

The filter is at 83% pass rate (4,149 / 4,998 files). The remaining
849 failures are proofs that reference dissolved content. Top patterns:

```
630 files  tactic 'rewrite' failed  — proof references dissolved declaration
264 files  failed to synthesize     — missing typeclass instance
 90 files  rewrite variant          — same root cause
```

To get to zero errors, add compression methods to `Extractor._emit_block()`:
- Dependency analysis: if a genuine proof references a dissolved decl,
  either keep the decl or rewrite the proof
- Typeclass resolution: if a `failed to synthesize` comes from a stripped
  instance, keep the instance
- Proof simplification: if `by simp` closes after removing ≠ 0, collapse

Each pattern is a method. Add it, run the pipeline, errors drop.

## Progression: Go Straight to Mathlib

Mathlib is the demo. Origin is production. The sketches are done.
The foundation is done. The next step: go straight to Mathlib,
file by file, domain by domain, and write only what's genuinely new.

### What's done

1. ✅ **The foundation.** Core.lean. 124 lines. Theorem + instances + simp set.
2. ✅ **The sketches.** 14 domain files. Definitions + key demonstrations.
3. ✅ **Physics.** 6 domains demonstrated. 86 hypotheses dissolved.
4. ✅ **Logic.** Liar, Russell, Curry unified. `no_some_fixed_point`.
5. ✅ **Val evidence.** 14,474 lines. The proof it works at scale.
6. ✅ **Pipeline.** `origin2.py run` — extract, build, report. Production UI.
7. ✅ **Class-based script.** Parser, Classifier, Extractor, Pipeline, UI.
8. ✅ **Three classifications.** Genuine (138K), dissolves (6K), conflates (1K).
9. ✅ **Ring finding.** Option α is not a Ring. Lean verified. Load-bearing.
10. ✅ **83% pass rate.** 4,149 / 4,998 files build clean. 849 remaining.

### What's next: run the pipeline

```bash
python3 scripts/origin2.py run
```

The script encodes all classification, extraction, and build logic.
Read the script to understand how it works. Improve the script to
fix what's broken. Do not do manual work.

The `classifications/` directory is historical documentation of the
Val-era mapping. It describes Val, not Origin. Ignore it.

### The pipeline: `origin.py run`

One command. Run it. Everything either builds or it tells you
exactly what to fix in the script.

```bash
python3 scripts/origin2.py run
```

What it does:

1. **Extract every Mathlib domain.** Runs `extract --domain` for
   each domain in Mathlib. Outputs to `Origin/Mathlib_<domain>/`.

2. **Build every extracted file.** Runs `lake build` on each.
   Collects pass/fail per file.

3. **Group errors by pattern.** If 200 files fail because the parser
   doesn't handle `@[to_additive]`, that's one script fix, not 200
   manual fixes. The report says: "142 files fail with
   `unknown constant AddAction.period` — root cause: multiline
   attribute parsing."

4. **Report.** What built, what failed, why. Grouped by root cause.

5. **Count lines.** Mathlib total lines vs Origin total lines.
   This is the proof.

The workflow:

```
run → read report → fix script → run again
```

Repeat until zero failures. Then the line count is the proof.

**Error grouping is the key.** Each unique error pattern maps to one
script improvement. Fix the script, not the output. Re-run. The
fixed pattern should produce zero errors. If 200 files had the same
error and your fix resolves it, 200 files now build clean.

**The final output:**

```
Mathlib:    2,200,000 lines
Origin:         X,XXX lines
Reduction:       XX.X%
Build:        PASS (0 errors)
```

That's the proof. Lean's kernel verified every line. The line counts
are objective. The build succeeds or it doesn't.

### The goal

Take a 2.2 million line library and express the same mathematics in
99%+ less code. Every theorem. Exhaustively. Building clean. In the
absolute minimum lines that Lean's richest functionality allows.

Origin is the 40-year veteran who takes what the new contributors
produce (Mathlib) and compresses it to the minimum expression. The
script is the veteran's expertise encoded as automation. Mathlib
grows. Origin consolidates. The script is the bridge.

The exhaustive conversion IS the proof. Cherry-picking easy theorems
proves nothing. Going through every theorem in Mathlib and showing
it builds on Origin in fewer lines — that's the evidence no one can
argue with. Lean's kernel verifies it. The line counts are objective.
The build succeeds or it doesn't.

Mathlib is the demo. Origin is production.
