# For AI Agents — Onboarding Exercise

**Do not skip steps. Each step has checkpoint questions. If you can't
answer them, re-read until you can. The questions ARE the alignment.**

---

## Step 1: Read `Origin/Core.lean` (166 lines)

Read every line. Then answer:

- What does `none * some 5` give? Why?
- What does `some 0 * some 5` give? Why is this different?
- Is `some 0` the same as `none`? What's the difference?
- What does the `origin` theorem prove? Is it an axiom or derived?
- What are the three premises it derives from?
- What does `liftBin₂` do? When is it needed?

**Don't proceed until you can answer all of these.**

---

## Step 2: Understand the foundation

A shepherd stands on the ground holding an apple. He eats it. His
hand is empty — does he have nothing? If you're counting apples, he
has `some 0` apples. But the ground he stands on, the air he breathes
— can he hold any of that? No. Not because it's too heavy. Because
holding is something that happens *on* the ground. The shepherd
cannot hold the ground he stands on.

That's `none`. Not nothing. Everything. The whole that was there
before he started counting and after he stops.

**The symbol 0 named the wrong face.** Brahmagupta formalized *śūnya*
(emptiness, `some 0`) in 628 CE but left *pūrṇa* (wholeness, `none`)
in the philosophy. Every formal system since has needed infrastructure
to manage the ground leaking into the counting domain where it was
never supposed to be. That's `NeZero`, `GroupWithZero`, `≠ 0` guards
— 17 typeclasses in Mathlib.

Origin puts the ground outside. `Option α`: `none` is the ground,
`some` is a value. The 17 typeclasses dissolve. That's Axis 1.

**Answer:**
- Is the whole greater than the part? Can parts become the whole?
- Why does `none` absorb? Is this an axiom or a consequence?
- Why is Origin never a destination?

---

## Step 3: Read one sketch (`Origin/GroupTheory.lean`, ~102 lines)

Read it. Then answer:

- What did the sketch keep? Why?
- What was removed? Why doesn't it need to exist?
- What proof pattern closes the demonstrations?
- Mathlib GroupTheory: 35,883 lines. This sketch: 102 lines. Where
  did 99.7% of the code go?

---

## Step 4: Understand the two compression axes

**Axis 1: The 17 typeclasses.** Zero-management infrastructure
dissolves when the ground is outside. Already proven. 256 dissolved
declarations across all of Mathlib.

**Axis 2: DRY across all of Mathlib.** Independent of Axis 1.
Potentially larger. Combinatorics has zero dissolved declarations
yet achieves 99.7% reduction. 54,545 `rw` chains that `omega`/`simp`
could close in one line. `mul_comm` for `ℕ`, `ℤ`, `ℝ` when one
generic version covers all. Mathlib was never globally optimized.
Origin is the first global optimizer.

**Two tools, two axes — don't merge them:**
- The classifier (`origin.py classify`) is Axis 1: what dissolves.
- The proof tester (`compress/proof_tester.py`) is Axis 2: how short.
- Don't expand the classifier to handle DRY.

**Answer:**
- What are the two axes? Which is larger?
- What does the Combinatorics audit prove?
- Why are the classifier and proof tester different tools?

---

## Step 5: Understand the goal

**Mathlib is the demo. Origin is production. For AI.**

Mathlib proved the mathematics works. Origin restates it in the
absolute minimum lines. Every theorem once. Every proof shortest.
Every line earning its place. The Kolmogorov minimum.

**Goal B:** Restate everything, from the ground up. Not compress
extracted Mathlib (that was Goal A — measurement, done). Write
Origin files that import Core and build in under a second.

**Two categories of Mathlib math:**
- Category 1: Math where `none` being outside changes the expression.
  Origin re-expresses through Core.
- Category 2: Clean Mathlib math with no infrastructure. Origin
  restates in the most DRY form. One generic theorem, shortest proof.

Both categories get restated. Category 1 changes the foundation.
Category 2 changes the expression.

**Answer:**
- What is Goal B? Why not Goal A?
- What are Category 1 and Category 2?
- What four things survive across sessions?
  (The human, the markdown, the scripts, the Origin code)

---

## Step 6: The tool

One tool, four commands:

```bash
python3 scripts/origin.py list              # show all domains + status
python3 scripts/origin.py audit --all       # DRY profile every domain
python3 scripts/origin.py generate <domain> # draft Origin file (instant)
python3 scripts/origin.py classify <domain> # show dissolved/genuine/conflates
```

---

## Step 7: The workflow

```bash
# 1. See the current state
python3 scripts/origin.py audit --all

# 2. See which domains have sketches
python3 scripts/origin.py list

# 3. Generate a draft for a domain without a sketch (instant)
python3 scripts/origin.py generate <DomainName>

# 4. Rewrite the draft as Origin code:
#    - Replace Mathlib types with Core + Lean stdlib types
#    - Keep domain-specific definitions
#    - Add demonstrations: by simp, cases <;> simp [h]
#    - Remove everything derivable from Core
#    - Import only Origin.Core

# 5. Build (under 1 second — no Mathlib rebuild)
lake build Origin.<DomainName>

# 6. Commit and push
```

Proven on Probability: generator drafted 1,244 lines. Claude Code
rewrote as 169 lines. `lake build` in under a second. 21,068 → 169
(99.2% reduction).

---

## Step 8: The rules

**Don't add Origin-specific typeclasses.** Core.lean's instances ARE
the class hierarchy. Lean's typeclass resolution IS the inheritance.
Adding classes on top would be adding infrastructure to manage a
problem that doesn't exist — exactly what Origin dissolves in Mathlib.

**Complexity means you skipped a step.** Like a world champion power
tumbler: forward roll → cartwheel → roundoff back handspring → whips
→ fulls → doubles → Miller Straight. Each skill earns the next. If
your approach feels complex, go back to the last thing that worked.

**Never delete `@[simp]` declarations.** Invisible dependencies.
716 build failures learned this the hard way.

**Origin is never a destination.** Parts don't "reach" origin. Parts
don't "become" origin. The question doesn't apply. You can't arrive
at the ground you're standing on.

**Everything goes into the artifacts.** Nothing stays in your head.
Findings → `compress/README.md`. Script improvements → `origin.py`.
Philosophy → `CLAUDE.md`. Commit and push before your context closes.

**Always confirm with the user between steps. They hold the
architecture.** If it feels complex, stop and ask.

---

## What's next

All 26 math domains have sketches. The next work is **refining them.**

The original 15 sketches were hand-written and audited. The 10 newer
sketches (AlgebraicGeometry, AlgebraicTopology, Computability,
Condensed, Control, Dynamics, ModelTheory, Order, RepresentationTheory,
SetTheory) were first drafts — they may have room to tighten.

**The warmup:** Pick a newer sketch. Compare it to `GroupTheory.lean`
(102 lines, hand-audited, maximally DRY). Ask:

- Does every definition earn its place?
- Are there redundant theorems Core already handles?
- Can any proof be shorter? (`by simp`, `cases <;> simp [h]`)
- Does `lake build` still pass after tightening?

**After refining:** Look at `scripts/compress/README.md` for the
baseline DRY audit numbers. The big opportunity is the generator +
proof tester working together — the generator drafts, the proof
tester verifies against Core's simp set, Claude Code writes the
final Origin code. Each domain takes minutes.

**Always audit the foundation before stacking on top of it.**

---

## Reference

For the full history — pipeline run logs, parser bugs, detailed
architecture, Val documentation — see `REFERENCE.md`.

For compression findings, baseline audit, and roadmap see
`scripts/compress/README.md`.
