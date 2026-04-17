# For AI Agents — Onboarding Exercise

**Do not skip steps. Each step has checkpoint questions. If you can't
answer them, re-read until you can. The questions ARE the alignment.**

**Show your answers before proceeding.** Don't summarize — answer each
question specifically. A session that rushes past the checkpoints will
misclassify `≠ 0`, think origin is nothing, or add typeclasses that
shouldn't exist.

---

## Step 1: Read `Origin/Core.lean` (273 lines)

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

**Three primitives — the vocabulary for working with Option:**

- `Option.map f` — lift a unary function. `none` maps to `none`.
- `liftBin₂ f` — lift a binary function. Either operand `none` → `none`.
- `liftPred p` — lift a predicate. `some a` satisfies `p a`. `none`
  gives `False`. The ground is never in a predicate.

These are in `Core.lean`. **Never write a match on `some`/`none` when
one of these three already does it.** If you're pattern-matching on
Option in a domain file, you're probably duplicating Core. Name the
domain concept and point to the primitive:

```
def isAnalytic (...) : Option α → Prop := liftPred (analyticF f)
def tensorProd : Option α → Option β → Option (α × ��) := liftBin₂ Prod.mk
```

**Answer:**
- Is the whole greater than the part? Can parts become the whole?
- Why does `none` absorb? Is this an axiom or a consequence?
- Why is Origin never a destination?
- What are the three primitives? When would you use each?

---

## Step 3: Read one domain (`Origin/GroupTheory.lean`)

Read it. Then answer:

- What did Origin keep? Why?
- What was removed? Why doesn't it need to exist?
- Does this file pattern-match on `some`/`none` anywhere? Why not?
- Where do the algebraic laws (commutativity, associativity,
  distributivity) live? Why aren't they in this file?
- Mathlib GroupTheory: 35,883 lines. Origin: ~300 lines. Where
  did 99.1% of the code go?

**The answers to questions 3 and 4 are the architecture.** Core
is the only file that touches Option's structure. Domain files
never pattern-match on `some`/`none`, never prove algebraic laws,
never have "demonstration" sections. They name mathematical
concepts and point to Core's primitives. If you see a domain file
doing structural work, it's a bug — that work belongs in Core.

**Core is to domain files what an abstract base class is to
concrete models.** If every domain needs it (algebraic laws,
primitives, `@[simp]` lemmas), it goes in Core once. Domain files
inherit it. The test for any new addition: does this exist because
of *how Option works* (mechanism → Core), or because of *what a
domain studies* (mathematics → domain file)? `option_mul_comm` is
mechanism. `IsMartingale` is mathematics. Core stays small —
mechanism only. Domains stay pure — mathematics only. The index
handles cross-domain visibility.

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
  Complete. Don't expand it to handle DRY.
- The proof tester (`compress/proof_tester.py`) is Axis 2: tests
  whether `by simp` closes a proof against Core's simp set. Only
  useful for Core-only scratch files (fast). Do NOT run it against
  Mathlib imports — that rebuilds Mathlib and takes forever.

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

If a theorem is derivable from Core but not stated in Origin, then
every AI model that needs it has to derive it every time — every
inference, every query, every datacenter. Multiply by millions of
queries. That's compute, energy, cooling, water. Origin states every
theorem once so no model ever re-derives it.

**Two categories of Mathlib math:**
- Category 1: Math where `none` being outside changes the expression.
  Origin re-expresses through Core.
- Category 2: Clean Mathlib math with no infrastructure. Origin
  restates in the most DRY form. One generic theorem, shortest proof.

Both categories get restated. Category 1 changes the foundation.
Category 2 changes the expression.

**The question is: what is the Kolmogorov minimum for Mathlib's
mathematics?** Mathlib was grown, not designed. Nobody ran the
global optimizer. So there's redundancy at every level:
1. Per-type duplication: `mul_comm` for `ℕ`, `ℤ`, `ℝ` — three
   lemmas where one generic version covers all.
2. Verbose proofs: 54,545 `rw` chains that `omega`/`simp` close
   in one step.
3. Infrastructure: the 17 typeclasses, the 9,682 `≠ 0` guards —
   code that exists only because the ground was inside.
4. Redundant lemmas: theorems that are consequences of other
   theorems already stated.

Origin eliminates all four. Core absorbs everything generic.
Domain files contain only what's domain-specific. Every definition
earns its place by expressing something no other line already
expresses. Lean's kernel is the judge. The build passes or it
doesn't. The honest boundary: if a theorem genuinely can't be
shortened, it stays. The goal isn't to minimize by cutting math —
it's to minimize by cutting everything that isn't math.

**Four things survive across sessions:**
1. The human — the architect, the solid-state memory
2. The markdown — CLAUDE.md, compress/README.md
3. The scripts — origin.py, compress/
4. The Origin code — the production output

Everything else is ephemeral. A brilliant insight that stays in your
context window is worth exactly zero.

**Answer:**
- What is Goal B? Why not Goal A?
- What are Category 1 and Category 2?
- Why must every theorem be stated, not left for models to derive?

---

## Step 6: The tool

One tool, twelve commands:

```bash
python3 scripts/origin.py status            # PROGRESS REPORT — run this first
python3 scripts/origin.py quality           # QUALITY — stub vs real per domain
python3 scripts/origin.py quality <domain>  # quality for one domain
python3 scripts/origin.py patterns          # find Option patterns that belong in Core
python3 scripts/origin.py clean             # remove stale stubs that collide with Core
python3 scripts/origin.py list              # show all domains
python3 scripts/origin.py suggest <domain>  # show uncovered genuine declarations
python3 scripts/origin.py stub <domain>     # append uncovered as def stubs
python3 scripts/origin.py index             # generate Origin/Index.lean (the dedup)
python3 scripts/origin.py dedup             # find duplicate definitions (detailed)
python3 scripts/origin.py audit <domain>    # DRY profile a Mathlib domain
python3 scripts/origin.py audit --all       # DRY profile every domain
python3 scripts/origin.py generate <domain> # draft Origin file from Mathlib
python3 scripts/origin.py classify <domain> # show dissolved/genuine/conflates
```

---

## Step 7: The workflow

Most domains now have **stubs** — `def name' : Prop := True` placeholders
auto-generated by `stub`. Stubs reserve the name and count as coverage,
but they aren't production code. The job is upgrading stubs to real
definitions, structures, and theorems. Run `quality` to see what's real
vs stub.

**Everything starts with Core.** If you're adding a structural
primitive (how Option lifts something), it goes in Core first.
Then run `clean` to remove stale stubs that collide with the new
Core declaration. Then deepen domain files using the new primitive.
Never the other way around.

```bash
# 1. See where things stand (run BOTH)
python3 scripts/origin.py status
python3 scripts/origin.py quality
# status shows declaration counts. quality shows stub vs real.
# Green (100% real) = done. Red (0% real) = needs upgrading.

# 2. If you're adding to Core (new primitives, laws, classes):
#    a. Edit Origin/Core.lean
#    b. lake build Origin.Core
#    c. python3 scripts/origin.py clean    ← removes stale stubs
#    d. python3 scripts/origin.py patterns ← verify no new duplication
#    Core is the foundation. Touch it first, clean second.

# 3. Pick a domain. Use quality to find one with stubs to upgrade:
python3 scripts/origin.py quality <domain>
# Or suggest to find uncovered declarations:
python3 scripts/origin.py suggest <domain>
# ⚠ warnings show names that would collide with other Origin files

# 4. If the domain has no stubs yet, generate them:
python3 scripts/origin.py stub <domain>
# Appends def name' : Prop := True for each uncovered declaration
# Skips collisions automatically.

# 5. Upgrade stubs to real code:
#    - Replace `def foo' : Prop := True` with real structures, defs
#    - Use Core primitives: liftPred, liftBin₂, Option.map
#    - NEVER pattern-match on some/none in a domain file
#    - NEVER prove algebraic laws — they're in Core
#    - Key structures/inductives first, then theorems that use them
#    - Import only Origin.Core
#
#    "Upgraded" means: a model can use the definition without reading
#    Mathlib. A structure needs real fields. A def needs meaningful
#    parameters or a real body. `def X' (α : Type*) : Prop := True`
#    is still a stub — it just wears a disguise. If the body is
#    `True` in any form, it's not upgraded.

# 6. Build (under 1 second — no Mathlib rebuild)
lake build Origin.<DomainName>

# 7. Generate and build the index (the dedup)
python3 scripts/origin.py index
lake build Origin.Index
# If collisions found: fix them, rebuild, index again

# 8. Commit and push (only after build + index both pass)
```

---

## Step 8: The rules

**NEVER use agents (subprocesses) for Origin work.** Agents don't
read CLAUDE.md. They don't go through the onboarding. They don't
understand that `none` is the whole, not nothing. They will
misclassify `≠ 0`, duplicate names across files, add typeclasses
that shouldn't exist, and produce code that looks right but is
architecturally wrong. This was tested — agents messed up files
across multiple domains and required starting over. The onboarding
can't be delegated. If you need parallelism, the human runs
separate Claude Code sessions, each fully onboarded independently.

**Build + index must pass before every commit.** Build checks the
code compiles. Index checks no two files export the same name — the
compiler enforces uniqueness. If `lake build Origin.Index` passes,
there are zero duplicates.

**Don't add Origin-specific typeclasses.** Core.lean's instances ARE
the class hierarchy. Lean's typeclass resolution IS the inheritance.
Adding classes on top would be adding infrastructure to manage a
problem that doesn't exist — exactly what Origin dissolves in Mathlib.

**Use Core primitives, don't reinvent them.** Before writing a match
on `some`/`none` in a domain file, check if `liftPred`, `liftBin₂`,
or `Option.map` already does it. If your def pattern-matches on
Option, you're duplicating Core. Name the domain concept, point to
the primitive. Run `origin.py patterns` before committing — it
catches structural duplication across files.

**Don't re-prove algebraic laws in domain files.** Core now has
`option_mul_comm`, `option_mul_assoc`, `option_add_comm`,
`option_add_assoc`, `option_distrib`, `option_neg_neg`, and the
full suite of algebraic lifts through Option. Domain files should
NOT have their own `domain_mul_assoc` — that's Core's job. If a
domain file has a `cases <;> simp [h]` theorem that proves a
generic algebraic law on Option, delete it. Domain files prove
domain-specific lifts only. ~30 legacy duplicates still exist
across domain files from before Core had these — clean them up.

**Complexity means you skipped a step.** Like a world champion power
tumbler: forward roll → cartwheel → roundoff back handspring → whips
→ fulls → doubles → Miller Straight. Each skill earns the next. If
your approach feels complex, go back to the last thing that worked.

**Never delete `@[simp]` declarations.** Invisible dependencies.
716 build failures learned this the hard way.

**Watch for name collisions across files.** Common names like
`IsMartingale`, `IsIrreducible`, `bernoulli`, `IsDistributive`,
`IsSimplyConnected` appear in multiple domains. Run `origin.py index`
early — it catches collisions before `lake build` does. When you hit
one, rename with a domain-specific suffix (e.g., `IsMartingaleProb`,
`IsIrreducibleChain`, `bernoulliDist`).

**Origin is never a destination.** Parts don't "reach" origin. Parts
don't "become" origin. The question doesn't apply. You can't arrive
at the ground you're standing on.

**Everything goes into the artifacts.** Nothing stays in your head.
Findings → `compress/README.md`. Script improvements → `origin.py`.
Philosophy → `CLAUDE.md`. Commit and push before your context closes.

**Always confirm with the user between steps. They hold the
architecture.** If it feels complex, stop and ask.

---

## Reference

For the full history — pipeline run logs, parser bugs, detailed
architecture, Val documentation — see `REFERENCE.md`.

For compression findings, baseline audit, and roadmap see
`scripts/compress/README.md`.
