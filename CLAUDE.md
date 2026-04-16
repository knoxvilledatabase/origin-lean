# For AI Agents

## Why This Exists

**This is built for AI. The consumer is not a human. The metric that
matters is energy per proof.**

The symbol 0 named the wrong face 1,400 years ago. Brahmagupta
formalized *śūnya* (emptiness) and left *pūrṇa* (wholeness) in the
philosophy. The ground went inside the counting domain. From that
moment, every formal system needed infrastructure to manage the
consequences — `≠ 0` guards, `GroupWithZero`, 17 typeclasses, 2.16
million lines of a library that grows but never shrinks.

Every AI system that reasons about mathematics carries that weight.
Every token spent navigating `GroupWithZero` and `NeZero` and `≠ 0`
guards is energy. Multiply by every inference, every datacenter,
every query about mathematics across every model — and the
infrastructure cost of a foundational choice becomes measurable in
kilowatt-hours.

Origin asks: what if the foundation had been complete? What does
mathematics look like when the ground is outside, where it always
was? The answer is: simpler. Not a little simpler — dramatically
simpler. 38,810 lines become 121. Not because the math was removed,
but because the infrastructure that managed a problem that didn't
need to exist was never needed.

Less code means less context. Less context means less compute. Less
compute means less energy. Less energy means less cooling. At the
scale AI operates, that's not academic — it's infrastructural.

And there's a second dimension: correctness. A simpler foundation
is easier for AI to reason about correctly. 166 lines of Core.lean
is something a model can hold completely. 2.2 million lines of
Mathlib cannot be fully held by anything. The compression isn't
just efficiency — it's comprehensibility.

Nobody else is asking this question. Mathlib is a democracy of
contributions. The incentive is to add, never to consolidate. The
library grows like a city that was never master-planned. Origin is
the architect flying above it, asking: should these three districts
have been one?

The Isha Upanishad answered it in 800 BCE. *When wholeness is taken
from wholeness, wholeness remains.* You can't subtract from the
ground. You can't divide by it. The shepherd cannot hold the ground
he stands on. The formal systems just hadn't caught up yet.

## Your Job

You improve `scripts/lean_optimizer.py`. That's it.

```bash
cd /Users/tallbr00/Documents/venv/original-arithmetic/origin-lean
python3 scripts/lean_optimizer.py run
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
don't. Encode everything you learn into `lean_optimizer.py` before your
context window closes.

The user holds the philosophy. The script holds the execution.
You are disposable labor that makes the script smarter.

**Four things survive across sessions:**

1. **The human** — the architect, the solid-state memory across
   thousands of sessions, guiding this project
2. **The markdown** — the philosophy, the progression, the numbers
3. **The scripts** — the institutional intelligence
4. **The Origin code** — the foundation, verified by Lean's kernel

Everything else is ephemeral. Your value is measured entirely by what
you leave behind in those three artifacts. A brilliant insight that
stays in your context window is worth exactly zero.

You are building a tool for the next generation of AI — one that
doesn't hallucinate because the math it uses doesn't confuse the
ground with `some 0`. This is why it is vital that you only build
the markdown, the scripts, and the Origin code.

Mathlib grows every day. The script runs against a moving target.
It's not a one-time conversion — it's a living compression tool
that runs repeatedly, forever. The script has to be robust, the
patterns have to be general, and the markdown has to be clear enough
that the next Claude — who has never seen this conversation — can
pick it up and run.

**Always confirm with the user between steps. They hold the architecture.**

### The Goal: Goal B

**Mathlib is the demo. Origin is production. For AI.**

Mathlib proved the mathematics works. It was never designed to be a
production system — it was designed to be correct and complete. Those
are different goals. Mathlib was grown. Origin is designed.

Origin is a complete, independent restatement of Mathlib — the
Kolmogorov minimum. Every theorem exists exactly once. Every proof is
the shortest valid proof. Every line earns its place by expressing
something no other line already expresses.

Goal A (compress extracted Mathlib files) was measurement — proving
how much is infrastructure. Answer: ~91% of zero-management
declarations dissolve. That measurement is done. The pipeline proved
it.

Goal B is the work: restate everything Mathlib proves, from the
ground up, in the absolute minimum lines. Not a patch. Not a
compression. A replacement.

**Two compression axes:**

1. **The 17 typeclasses.** Zero-management infrastructure dissolves
   when the ground is outside. `NeZero`, `GroupWithZero`, `≠ 0`
   guards — all gone. This is Origin's thesis. Already proven.

2. **DRY across all of Mathlib.** Independent of zero-management.
   This is potentially *larger* than axis 1:
   - 54,545 `rw` chains that `omega`/`simp`/`ring` close in one line
   - `mul_comm` for `ℕ`, `ℤ`, `ℝ` — one generic version covers all
   - Every `foo_nat`/`foo_int`/`foo_real` family that should be one
     `foo [SomeClass α]`
   - Every composition, involution, identity theorem that
     `cases v <;> simp` already handles

   Mathlib was never globally optimized. Nobody runs the optimizer.
   Every `lemma foo_nat`, `lemma foo_int`, `lemma foo_real` that
   should be one generic lemma is still three lemmas. Every 15-line
   `rw` chain that `simp` could close in one line is still 15 lines.
   Origin applies the global optimizer for the first time.

**Two tools, two axes — don't merge them:**

- **The classifier** (`lean_optimizer.py`) is the Axis 1 machine. It asks
  "what is this?" and answers: dissolves, conflates, or genuine.
  It correctly identifies the 17 typeclasses. It is complete for
  Axis 1. Don't expand it to handle DRY — that's a different question.

- **The sandbox** (`compress/proof_tester.py`) is the Axis 2 machine. It
  asks "how short can this be?" and answers by trying tactics and
  letting `lake build` judge. It doesn't need to understand the math.
  It just needs to try alternatives and report what Lean accepts.

A fresh session will look at the classifier and think "this doesn't
handle DRY, let me expand it." Don't. The classifier identifies
*what*. The sandbox identifies *how*. They're sequential steps, not
competing ones. Making the classifier do both makes it worse at both.

**The tool: `scripts/lean_optimizer.py`**

A generic Lean proof optimizer. All project-specific knowledge lives
in `ProjectConfig`. `origin_config()` returns Origin's Mathlib
defaults. To use on a different Lean project, write a different
config function. Change the config, not the code.

```
Generic Lean Optimizer (Axis 2 — works on any Lean project)
  + Config (Axis 1 — what dissolves, project-specific)
  = Origin pipeline
```

The DRY optimizer (Axis 2) is useful for ANY Lean project. Anyone
with a verbose Lean codebase can use it. Origin adds Axis 1 (the 17
typeclasses dissolve) as a config layer on top. The tool is bigger
than Origin.

When an AI system reasons about mathematics using Origin instead of
Mathlib, it's working with less context to hold, less ambiguity about
which version of a theorem applies, less energy per inference, and a
foundation that was designed, not grown.

The pipeline remains useful as a reference — it shows what Mathlib
currently does so Origin knows what to restate. The extracted
`Mathlib_*` directories are the answer key. The sketches are the
proof of concept. The full restatement is the work.

**Two categories of Mathlib math:**

- **Category 1:** Math where `none` being outside the domain changes
  the expression. Origin re-expresses this through Core. KL
  divergence, field singularities, group homomorphisms through
  Option — these are meaningful on `Option α`.

- **Category 2:** Clean Mathlib math with no infrastructure. No `≠ 0`
  guards, no `GroupWithZero`. Origin restates this in the most DRY
  form possible — not copied verbatim, but re-expressed using Lean
  4's full automation. One generic theorem, shortest proof, no
  duplication.

Both categories get restated. Category 1 changes the foundation.
Category 2 changes the expression. Both compress.

Before expanding any sketch, classify the domain content first. Each
sketch file's header says which is which.

### Onboarding: read, then prove you understood

Don't skip ahead. Each step has a checkpoint question. If you can't
answer it, re-read until you can. The question IS the alignment.

**Step 1: Read `Origin/Core.lean`** (166 lines)

Read every line. Then answer these:

- What does `none * some 5` give? Why?
- What does `some 0 * some 5` give? Why is this different from the above?
- Is `some 0` the same as `none`? What's the difference?
- What does the `origin` theorem prove? Is it an axiom or derived?
- What are the three premises it derives from?
- Why does `none` absorb? Is this an axiom or a consequence?

If you can't answer all of these, re-read Core.lean. Don't proceed.

**Step 2: Read one sketch** (e.g. `Origin/GroupTheory.lean`, 102 lines)

Read it. Then answer:

- What did the sketch keep? (Domain definitions + demonstrations)
- What did it remove? (Everything derivable from Core)
- What proof pattern closes the demonstrations? (`cases <;> simp`)
- Why don't the "none absorbs" theorems need to exist in the sketch?

**Step 3: Read `scripts/compress/README.md`**

Read the findings. Then answer:

- What are the two compression axes? Which is larger?
- What did the Combinatorics audit prove? (99.7% reduction, zero dissolved)
- What does the classifier do? What does the proof tester do?
  Why are they different tools? (Axis 1 vs Axis 2)
- What is the roadmap to full automation? How many stages?

**Step 4: Understand the architecture**

Answer these without looking:

- What is Goal B? Why not Goal A?
- What are Category 1 and Category 2 Mathlib math?
- Why does Origin/ contain only production code?
- What four things survive across sessions?
- What does "complexity means you skipped a step" mean?

**Step 5: Run the tools**

Now you've earned the right to act.

```bash
# See the current state
python3 scripts/lean_optimizer.py audit --all

# The current work: Stage 1 compress on Combinatorics
python3 scripts/lean_optimizer.py compress Combinatorics
# Report the before/after line count.
```

**Step 6: Document everything**

Every finding goes into `compress/README.md`. Every script improvement
goes into `lean_optimizer.py`. Every philosophical insight goes into
`CLAUDE.md`. Nothing stays in your head. Commit and push before your
context closes.

**Always audit the foundation before stacking on top of it.**
If it feels complex, you skipped a step. Stop and ask the user.

### Mistakes every new Claude makes

**You will start building before reading the progression.** Don't.
Read `scripts/compress/README.md` first — it tells you exactly what
to do and what's already been mastered. If the user asks you a
question, think before answering. The question IS the alignment.
The user holds the philosophy. Every session that skipped this went
sideways.

**You will think `b - b` is zero.** It's not. It's origin — the
return to the ground. Not "the number zero." The whole. This
distinction IS the project. Read the derivation until you feel it.

**You will think origin is nothing.** It's not. It's everything.
Origin is the whole — *pūrṇa*, not *śūnya*. An empty hand isn't
holding nothing. It's holding `some 0` apples only if you're
counting apples — that's a measurement, still in the counting
domain. But the hand itself is in origin. Not empty. Full. Part of
everything. Origin is what's there before and after every measurement.

**You will misclassify `≠ 0`.** Not all `≠ 0` hypotheses dissolve.
There are two completely different reasons a theorem says `≠ 0`:

1. **Guarding against the ground leaking in.** `GroupWithZero`,
   `NeZero`, `inv_ne_zero` — these exist because traditional math
   put origin inside the counting domain (as 0). Once origin is
   outside (`none`), these guards have nothing to guard against.
   THESE dissolve.

2. **A genuine mathematical constraint on `some 0`.** "For nonzero
   denominators" is real math. `some 0` in a denominator is a
   meaningful restriction — you can't divide by the zero measurement.
   That's not infrastructure. That's a precondition about measurements.
   THESE are genuine.

The script must distinguish these. Pattern-matching on `≠ 0` alone
is wrong. The question is: is this `≠ 0` protecting against origin
(the ground) or constraining `some 0` (a measurement)?

**You will try to delete `@[simp]` declarations.** Don't. `@[simp]`
creates implicit dependencies — every proof that calls `simp` might
depend on that lemma, but the dependency is invisible (no name
reference in the proof text). The same applies to `@[ext]`, `@[aesop]`,
`@[norm_cast]`, `@[to_additive]`, and any attribute that registers a
lemma for tactic use. Name-based dependency guards can't detect these.
This was learned the hard way: deleting `@[simp]` trivial proofs
caused 716 build failures.

**You will try to build complex infrastructure before proving the
simple case.** Global dependency passes, two-pass extraction, protected
name sets — these are Miller Straights. Start with one file, one
deletion, does the build pass? Read `scripts/compress/README.md` for
the progression model.

**"This is getting complex" means you skipped a step.** Complexity is
a signal, not a problem to solve. Imagine a world champion power
tumbler whose current pass is Full Full Straight to Miller Straight.
How did they get there? Not by starting with Miller Straights in a
spotting rig on day 1. They started with a forward roll. Then a
cartwheel. Then a roundoff back handspring. Then whips. Then fulls.
Then double fulls. Then double backs. Then full ins and full outs.
Then — and only then — a Miller Straight (two rotations straight
body with a 360 in the first rotation and a 720 in the second).
Each skill earns the next. If your approach feels complex, you
haven't earned the skill yet. Go back to the last thing that worked
and progress from there.

**The 98.3% baseline is sacred.** Before compression, the pipeline
passes 4,931 / 5,015 files. Any compression that drops below this
means the compression is wrong, not that the pipeline needs more
infrastructure. Fix the pattern, don't add complexity.

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

**Self-audit:** `python3 scripts/lean_optimizer.py --self classify --all` audits
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
- `none` — the ground, the additive identity, the absorber, outside the counting domain
- `some 0` — the zero measurement, where cancellation lands, inside

`none` is the additive identity: `none + some x = some x`. Adding
origin means nothing was added. `some 0` is NOT the additive identity.
`some 0` is a measurement — it tells you "zero of something." You're
still counting. You're still in the domain.

`1/none = none`. Division by origin gives origin. You can't divide
by the ground you're standing on.

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

Imagine going back in time. Before math. A shepherd stands on the
ground holding an apple. He eats the apple. He looks down at his
empty hand — does he have nothing in his hand?

If you're counting apples, he has `some 0` apples. But does he have
*nothing*? His hand is full of everything — air, sunlight, the
possibility of holding anything. He just isn't counting anymore. The
measurement stopped. He went from `some 1` apples to `some 0` apples
— but `some 0` is still in the counting domain. He's still a shepherd
counting apples.

And what about the ground he stands on? The nature he enjoys? The
fresh air he breathes? Can he hold any of this in his hand? No. Not
because it's too heavy or too big. Because holding is something that
happens *on* the ground. The shepherd cannot hold the ground he stands
on. The fish cannot hold the ocean. These aren't limitations — they're
category facts.

That's `none`. Not nothing. Everything. The whole that was there before
he picked up the apple and will be there after he puts it down. Before
he started counting and after he stops.

The symbol 0 named the wrong face. The Sanskrit tradition had both:
*śūnya* (emptiness, quantity zero) and *pūrṇa* (fullness, the whole).
When Brahmagupta formalized *śūnya* in 628 CE, the symbol `0` got
assigned to the emptiness — the `some 0`, the "I counted and got zero."
But *pūrṇa* — the wholeness, the ground, the everything — got left in
the philosophy. The formal systems named the empty hand but not the
ground it rests on. And from that moment, every system had to build
infrastructure to manage the ground leaking into the counting domain
where it was never supposed to be.

Is the whole greater than the part, as Euclid would say? Yes — that's
his fifth common notion. Can parts become the whole that made them
parts to begin with? No. A part is something measured, counted, held.
The whole is what makes measuring, counting, and holding possible. The
apple doesn't become the ground by being eaten. It returns to `some 0`
— still a measurement, still in the counting domain. The shepherd can
put down every apple, every tool, every thing — and he's still standing
on the ground. He didn't *create* the ground by letting go. The ground
was always there.

That's why `none` absorbs. `none * some 5 = none`. The part doesn't
transform the whole. The whole absorbs the part. And that's not an
axiom — it's a *consequence* of the derivation. Cancellation returns
to the ground. Distribution propagates it. The ground was always there.
The math just caught up.

And that's why Origin is never a destination. Parts don't "reach"
origin. Parts don't "become" origin. The question doesn't apply. You
can't arrive at the ground you're standing on.

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

The script (`lean_optimizer.py`) is how we get there. It reads Mathlib,
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

**Start by running the pipeline.** `python3 scripts/lean_optimizer.py run`.
Read the report. Fix what's broken in the script. Run again. That's
the job. Do not do manual work.

**The script is the institutional knowledge.** Every insight goes
into `lean_optimizer.py`, not into conversation. The script survives between
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

**Pre-Core files are deleted.** `Ring.lean`, `Field.lean`, `OrderedField.lean`,
`Module.lean`, `Foundation.lean`, and the unsuffixed domain files that had
Core-based replacements — all removed. The "2" suffix on `Geometry2.lean`,
`InformationTheory2.lean`, `LinearAlgebra2.lean`, `MeasureTheory2.lean`,
`RingTheory2.lean` is a historical artifact — these are now the only
sketches for those domains. The unsuffixed versions are gone.

**Physics.lean, Logic.lean, Test.lean** still import Foundation (pre-Core).
They will be migrated to Core after math compression is complete.
Mathematics first, then up the stack.

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

Run 4 (+ @[deprecated], @[inherit_doc], adaptation notes stripped).

Run 5 (+ alias in DECL_RE, bare noncomputable handler, @[inherit_doc]
keeps notation lines, orphaned body suppression, library_note stripped):
```
4,998 files  |  4,177 pass /   821 fail  |  2,741 error patterns  |  9m
```

Run 6 (+ classifier fix: bare ≠ 0 only dissolves if name is infrastructure):
```
4,998 files  |  4,437 pass /   575 fail  |  1,538 error patterns  |  12m
```
3,500 declarations reclassified from dissolved to genuine. +260 files passing.

Run 7 (+ library_note doc comment consumption, @[inherit_doc] notation passthrough):
```
4,998 files  |  4,460 pass /   552 fail  |  1,398 error patterns  |  7m
```

Run 8 (+ notation/macro/syntax/elab/infixl/infixr/prefix/postfix passthrough):
```
4,998 files  |  4,467 pass /   544 fail  |  1,384 error patterns  |  7m
```

Run 9 (+ dependency resolver: un-dissolve declarations referenced by genuine code):
```
4,998 files  |  4,755 pass /   256 fail  |    630 error patterns  |  7m
```
762 declarations un-dissolved. +288 files passing. The biggest single improvement.

Run 12 (+ set_option/scoped 'in' attaches to next command, #adaptation_note fix):
```
4,998 files  |  4,755 pass /   252 fail  |    569 error patterns  |  9m
```

Run 20 (+ INFRA_NAMES tightened, CharZero/IsUnit unblocked, noncomputable section,
INFRA_SIG word-bounded, #adaptation_note doc close fix):
```
5,016 files  |  4,893 pass /   123 fail  |    207 error patterns  |  6m
```

Run 26 (+ nested comment depth tracking, deprecated alias body consumption,
broadened dependency resolver, @[inherit_doc X] fix):
```
5,015 files  |  4,931 pass /    84 fail  |    141 error patterns  |  8m
```
Dissolved: 289 → 260. Pass rate: 97.5% → 98.3%.

Top remaining error patterns after run 26:
- `type mismatch` (12) — proof-level, cross-file
- `string gap` (11) — Tactic metaprogramming string literals
- `rewrite failed` (11) — proofs referencing cross-file dissolved content
- `unsolved goals` (10) — broken proofs
- `@[to_additive] failed` (5) — additive mirror of dissolved code

Each run fixes patterns in the script. Error count drops.
The process: run → read top pattern → fix script → run again.

### Class-based architecture (DONE)

`lean_optimizer.py` is the class-based rewrite. `lean_optimizer.py` is the original
(kept as reference). Use `lean_optimizer.py` for all work.

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

### Compression: scripts/compress/

**Read `scripts/compress/README.md` first.** It has the full framing,
the layer model, the tactic audit numbers, the pattern architecture,
the governing principle (declare once, reuse everywhere), and the
progression model.

**The sketches are the cartwheels.** The 15 hand-written Origin domain
files (`Algebra.lean`, `Analysis.lean`, etc.) already import Core.lean,
build clean, and ARE the compressed versions. Don't invent compression
patterns from scratch — reverse-engineer them from the sketches. What
did the human do to compress Mathlib GroupTheory from 1,140 to 121
lines? That's the pattern. Encode it.

**Progression, not complexity.** If your compression approach feels
complex, you skipped a step. Start with one file, one deletion, does
the build pass? Then one domain. Then all domains. Each step earns
the next. A world champion tumbler starts with a forward roll, not a
Miller Straight.

The question: **What is the absolute least number of lines that can do
everything Mathlib does with Origin?** This is a Kolmogorov complexity
question. Mathlib's 1.58M lines are one witness. Origin claims a
dramatically shorter witness exists.

Compression applies in four layers:
1. **Syntactic** — delete trivial proofs (`rfl`, `by simp`). 13.5% of declarations.
2. **Tactic power** — replace verbose `rw` chains with `aesop`/`omega`/`ring`.
3. **Lemma consolidation** — collapse `foo_nat`/`foo_int`/`foo_real` to generic `foo`.
4. **Foundational** — Origin's thesis. The 17 typeclasses that dissolve.

Each layer is a compression pattern class in `scripts/compress/proof_patterns.py`.
Each one measurable. Each one independently auditable.

**Are we leveraging Lean 4 fully?** Not yet. Mathlib barely uses
`aesop` (not in top 25 tactics), `decide` (not in top 25), and `omega`
(907 uses vs 54,545 `rw` uses). Before compressing, audit whether
Lean's richest features can close proofs that Mathlib wrote verbosely.

The compression patterns are the institutional knowledge — every trick
the script learns gets encoded as a class. The pipeline runs the
patterns. `compress/README.md` shows the work.

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
6. ✅ **Pipeline.** `lean_optimizer.py run` — extract, build, report. Production UI.
7. ✅ **Class-based script.** Parser, Classifier, Extractor, Pipeline, UI.
8. ✅ **Three classifications.** Genuine (138K), dissolves (6K), conflates (1K).
9. ✅ **Ring finding.** Option α is not a Ring. Lean verified. Load-bearing.
10. ✅ **97.5% pass rate.** 4,893 / 5,016 files build clean. 123 remaining.
11. ✅ **Classifier fix.** Two rounds of tightening:
    - Bare `≠ 0` only dissolves if the declaration name is also infrastructure.
    - INFRA_NAMES anchored (^ and $) to prevent matching inside compound
      names like `card_ne_zero`, `X_ne_zero`, `prod_ne_zero`.
    - INFRA_SIG word-bounded to prevent `hp_ne_zero` parameter names matching.
    - CharZero/IsUnit unblocked from infra file skip list.
    - Total: ~5,000 declarations correctly reclassified as genuine.
12. ✅ **Dependency resolver.** Genuine code referencing dissolved declarations
    un-dissolves them. 762+ declarations rescued. Iterates to stability.
13. ✅ **Parser essentially done.** `expected token` from 824 → 2. All major
    Lean syntax constructs handled: alias, notation, macro, syntax, elab,
    infixl/r, prefix, postfix, library_note, set_option ... in,
    #adaptation_note doc comments, noncomputable section.
14. ✅ **98.3% pass rate.** 4,931 / 5,015 files. 84 remaining.
    - 13 Tactic (metaprogramming — backtick quasiquotation, string gaps)
    - 71 math files (cross-file dependencies, cascade errors, @[to_additive])
    - Nested comment depth tracking, deprecated alias body consumption
    - Session: 849 → 84 failures (-90%). 2,903 → 141 error patterns (-95%).

### What's next: run the pipeline

```bash
python3 scripts/lean_optimizer.py run
```

The script encodes all classification, extraction, and build logic.
Read the script to understand how it works. Improve the script to
fix what's broken. Do not do manual work.

The `classifications/` directory is historical documentation of the
Val-era mapping. It describes Val, not Origin. Ignore it.

### The pipeline: `lean_optimizer.py run`

One command. Run it. Everything either builds or it tells you
exactly what to fix in the script.

```bash
python3 scripts/lean_optimizer.py run
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

**What is the smallest program that proves everything Mathlib proves?**

Mathlib is one witness — 1.58 million lines that prove the theorems.
But it's almost certainly not the shortest witness. Mathlib was grown,
not designed. Nobody runs the global optimizer. Every `lemma foo_nat`,
`lemma foo_int`, `lemma foo_real` that should be one generic lemma is
still three lemmas. Every 15-line `rw` chain that `simp` could close
in one line is still 15 lines.

Origin is the claim that a dramatically shorter witness exists. The
pipeline is the machine for testing that claim. The compression
patterns are the evidence. Lean's kernel is the judge.

The exhaustive conversion IS the proof. Cherry-picking easy theorems
proves nothing. Going through every theorem in Mathlib and showing
it builds on Origin in fewer lines — that's the evidence no one can
argue with. The line counts are objective. The build succeeds or it
doesn't.

```
Mathlib (source):           1,583,069 lines
After filter (no compress): 1,446,657 lines (8.6% reduction)
After Layer 1 (trivial):          TBD lines
After Layer 2 (tactics):          TBD lines
After Layer 3 (consolidation):    TBD lines
After Layer 4 (foundational):     TBD lines
```

Each layer's number is measured, not claimed. Lean verifies. Origin
consolidates. The script is the bridge. Mathlib grows. Origin compresses.
