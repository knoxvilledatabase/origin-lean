# Compression Patterns

## The Question

**What is the absolute least number of lines that can do everything
Mathlib does with Origin?**

This is a Kolmogorov complexity question. Mathlib's 1.58 million lines
are one witness — one program that proves the theorems. But it's almost
certainly not the shortest witness. Mathlib was grown, not designed.
Nobody runs the global optimizer. Every `lemma foo_nat`, `lemma foo_int`,
`lemma foo_real` that should be one `lemma foo [SomeClass α]` is still
three lemmas.

Origin is the claim that a dramatically shorter witness exists. This
directory is the machine for finding it.

## The Principle: Declare Once, Reuse Everywhere

No two lines of code should do the same thing. Every declaration
exists exactly once. This applies at every level:

**In the Lean output:**
- One generic `theorem foo [SomeClass α]`, not three `theorem foo_nat`,
  `theorem foo_int`, `theorem foo_real`
- One `cases <;> simp [h]`, not a 15-line `rw` chain
- One instance declaration, never a wrapper around it
- If Core.lean already proves it, it doesn't exist in the output

**In the Python script:**
- One compression pattern class, applied to every file forever
- One classifier rule, never duplicated across methods
- One pipeline, never hand-edited output

**In the repository:**
- One source of truth per concept — `Core.lean` for the foundation,
  `CLAUDE.md` for the philosophy, `compress/README.md` for compression
- The sketches are the design target — if a `Mathlib_*` file matches
  a sketch, the sketch wins and the extracted version disappears

The deepest expression: Mathlib has `lemma mul_zero` as an axiom in
`MulZeroClass`. Origin has it as a consequence of three lines in
`Core.lean`. Mathlib declared it once per type, per typeclass, per
variant. Origin declares it once, for everything, forever.

The answer to "what is the absolute least number of lines" is the
number you get when every declaration exists exactly once and nothing
is repeated at any level of the stack.

## The Foundation Already Mastered

Before compression begins, these levels were completed and proven.
**If compression breaks something at these levels, the compression
is wrong — not the foundation.** Go back and fix the compression.

### Level 1: Core.lean (DONE)
The `origin` theorem, instances for `*` `+` `-` on `Option α`, the
`@[simp]` set, `liftBin₂`, `no_some_fixed_point`. 166 lines. The
entire algebraic foundation.

### Level 2: Parser (DONE — origin2.py)
Reads Mathlib files into blocks. Handles all major Lean 4 syntax:
alias, notation, macro, syntax, elab, infixl/r, prefix, postfix,
library_note, set_option ... in, #adaptation_note, nested comments,
deprecated aliases. `expected token` errors: 824 → 2.

### Level 3: Classifier (DONE — origin2.py)
Distinguishes ground guards from measurement constraints. `≠ 0` in
a field theory theorem is genuine math about `some 0`. `NeZero` and
`GroupWithZero` in a signature are infrastructure. INFRA_NAMES anchored
with word boundaries. INFRA_SIG word-bounded. 5,713 → 260 dissolved.

### Level 4: Dependency resolver (DONE — origin2.py)
Within-file: if a genuine proof references a dissolved declaration,
un-dissolve it. Iterates to stability. Checks all block types.
762+ declarations rescued.

### Level 5: Extraction pipeline (DONE — origin2.py)
98.3% pass rate. 4,931 / 5,015 files build clean. 84 remaining
(13 Tactic metaprogramming, 71 cross-file cascade). `noncomputable
section` on all extracted files. Parallel build across 10 cores.

### Level 6: The sketches (DONE — hand-written)
15 Origin domain files import Core.lean and build clean. These ARE
the compressed versions. Written by the human to be maximally DRY.
They prove compression works at the single-domain level.

```
GroupTheory:   1,140 → 121 lines (89% compression)
Combinatorics: 1,349 → 105 lines (92%)
CategoryTheory: 1,069 → 93 lines (91%)
FieldTheory:     831 → 95 lines (89%)
```

## The Progression: Cartwheels Before Miller Straights

**Read this before writing any compression code.**

A world champion power tumbler doesn't start with a Miller Straight
(two rotations, 360 + 720). They start with a forward roll, then a
cartwheel, then a roundoff back handspring, then whips, then fulls,
then doubles, building up over years. Each skill earns the next.

**The sketches are the cartwheels and handsprings.** They're already
done. They prove the move is real. The compression work is encoding
what the sketches already demonstrate into patterns the script can
apply to ALL of Mathlib, not just the curated examples.

**Don't invent compression patterns from scratch.** Reverse-engineer
them from the sketches. What did the human do to turn 1,140 lines of
Mathlib GroupTheory into 121 lines of `GroupTheory.lean`? That's the
pattern. Encode it.

### The progression for each new compression pattern:

1. **Study one sketch** — read it, understand what makes it short
2. **Compare to its Mathlib_ counterpart** — what was removed, what
   was rewritten, what was generalized
3. **Identify the pattern** — is it deletion? tactic replacement?
   lemma consolidation? generalization?
4. **Encode the pattern** — add a class to `patterns.py`
5. **Test on one file** — does the build pass?
6. **Test on one domain** — does the domain pass?
7. **Test on all domains** — does everything pass?
8. **Measure the line count** — how many lines did this pattern save?

Each step earns the next. **If step 5 fails, don't attempt step 6.**
Fix the pattern until step 5 passes. If step 6 fails, don't attempt
step 7. The failure tells you the pattern needs refinement, not that
you need a more complex pipeline.

**If it feels complex, you skipped a step.** Global dependency passes,
two-pass extraction, protected name sets — these are Miller Straights.
Don't attempt them until single-file and single-domain compression
are proven and solid.

Does it make sense to do Calculus before Algebra? Algebra before
Arithmetic? No. Start with the simplest sketch, prove the pattern,
then progress to harder domains. The sketches tell you the order.

## The Sketch vs Mathlib: GroupTheory (reverse-engineered)

This is what the compression looks like, proven by hand.

```
Mathlib GroupTheory:  121 files, 38,810 lines, 4,195 declarations
Origin GroupTheory:     1 file,    121 lines,    18 declarations
```

### What the sketch KEPT (18 declarations)

| Category | Name | Why it exists |
|----------|------|---------------|
| DEFINITION | `GroupAxioms` | Domain-specific structure — Core doesn't define this |
| DEFINITION | `isSubgroup` | Domain predicate |
| DEFINITION | `isNormal` | Domain predicate |
| DEFINITION | `cosetEquiv` | Domain definition |
| DEFINITION | `isSylowSubgroup` | Domain definition |
| DEFINITION | `isSolvable` | Domain definition |
| DEFINITION | `isNilpotent` | Domain definition |
| DEFINITION | `isAbelian` | Domain predicate |
| DEFINITION | `IsFreeGroup` | Domain definition |
| DEFINITION | `isGroupAction` | Domain definition |
| DEFINITION | `isConjugate` | Domain definition |
| LIFT | `hom_comp` | `by cases v <;> simp` — demonstrates Option lift |
| LIFT | `hom_preserves_mul` | `by simp [h]` — demonstrates Option lift |
| LIFT | `group_none_mul` | `by simp` — demonstrates origin absorbs |
| LIFT | `group_mul_none` | `by simp` — demonstrates origin absorbs |
| LIFT | `group_some_mul` | `by simp` — demonstrates measurement works |
| LIFT | `group_neg_none` | `by simp` — demonstrates origin absorbs |
| LIFT | `group_neg_some` | `by simp` — demonstrates measurement works |

### What the sketch REMOVED (4,177 declarations)

| Count | Category | Why it was removed |
|-------|----------|--------------------|
| 3,259 | Genuine theorems | Core.lean's instances + simp set handles them |
| 400 | Instances | Core.lean already provides `Mul`/`Add`/`Neg` on `Option` |
| 349 | Simp lemmas | Core.lean's `@[simp]` set already has them |
| 140 | Trivial `rfl` | Lean's kernel reduces these automatically |
| 12 | Dissolved | Zero-management infrastructure |

### The pattern

The sketch keeps only two things:
1. **Domain-specific definitions** — structures, predicates, concepts
   that are unique to group theory and don't exist in Core.lean
2. **Key demonstrations** — a handful of `by simp` / `cases <;> simp`
   proofs showing that the Option lift works for this domain

Everything else is removed. The 3,259 genuine theorems aren't "deleted"
— they're DERIVABLE from Core.lean. The sketch doesn't need to state
them because Core.lean's instances and simp set already prove them.

**This is the compression pattern for every domain.** Keep definitions.
Keep demonstrations. Remove everything derivable.

## The Layers

Compression applies in four layers, from easiest to hardest:

### Layer 1 — Syntactic (easy, measurable now)

Redundant proofs: `rfl`, `by simp`, `by exact h`, `by norm_num`.
Declarations whose proof Core.lean's simp set already handles.
No mathematical insight required — just deletion.

**Measured (2026-04-15):** 21,649 / 160,525 genuine declarations
(13.5%) have trivial proofs. ~49,000 lines removable.

### Layer 2 — Tactic power (medium)

Replacing verbose `rw` + `simp` + `exact` chains with Lean 4's most
powerful automation: `aesop`, `omega`, `decide`, `ring`, `polyrith`,
`norm_cast`, `positivity`, `gcongr`. Accepting slower compile times
in exchange for shorter source.

**Lean 4 features Mathlib underuses:**
- `deriving` — auto-generate instances instead of writing them
- `@[ext]` — extensionality lemmas for free
- `aesop` — proof search (barely used in Mathlib: not in top 25 tactics)
- `decide` — computational proofs (barely used: not in top 25)
- `omega` — linear arithmetic (907 uses vs 54,545 `rw` uses)
- Custom tactic macros — a single `origin_simp` could replace patterns

**Mathlib tactic profile (160,525 genuine declarations):**
```
54,545  rw        — rewriting (dominant)
41,264  simp      — simplification
34,064  exact     — exact term
21,090  have      — intermediate goals
17,595  rfl       — reflexivity
16,347  refine    — partial proof terms
12,573  apply     — application
10,376  intro     — introduce hypotheses
 8,560  ext       — extensionality
 8,280  obtain    — destructuring
 1,138  ring      — ring identity
   907  omega     — linear arithmetic
   809  linarith  — linear arithmetic
   759  norm_num  — numerical normalization
```

### Layer 3 — Lemma consolidation (hard)

Many Mathlib lemmas are special cases of more general lemmas that
don't exist yet. Proving the general version makes dozens of specific
lemmas become one-liners or vanish entirely. This requires mathematical
insight, not just tactic swapping.

### Layer 4 — Foundational restructuring (Origin's thesis)

The 17 zero-management typeclasses. The conflation of ground and zero.
Option α separating what rings conflate. This is already measured:
5,713 → 260 dissolved declarations (95% of the infrastructure layer).

## Architecture

```
scripts/
  origin2.py              — the pipeline (extraction, classification, build)
  compress/
    __init__.py            — imports
    patterns.py            — every compression pattern as a class
    README.md              — this file (the "show your work" file)
```

**Three concerns, three locations:**
- `CLAUDE.md` holds the philosophy
- `origin2.py` holds the pipeline execution
- `compress/` holds the compression knowledge

Each pattern is a class inheriting `CompressionPattern`:

```python
class CompressionPattern:
    name: str
    description: str
    def match(self, block: Block) -> bool: ...
    def compress(self, block: Block) -> str | None: ...
```

The Extractor iterates registered patterns in order. First match wins.
Return `None` to delete. Return a string to replace. A dependency guard
prevents deletion of any declaration that non-trivial declarations
reference by name.

## How to add a pattern

1. Create a class in `patterns.py` inheriting `CompressionPattern`
2. Implement `match(block)` → bool and `compress(block)` → str | None
3. Add it to `get_patterns()`
4. Run `python3 scripts/origin2.py run`
5. Update this file with before/after numbers

## Foundation Audit (2026-04-16)

Before adding compression patterns, we audited whether Core.lean's
simp set already handles common sketch patterns. Tested in a scratch
file, `lake build` confirmed.

**Finding:** Three patterns that appear 17+ times across sketches all
close with `cases v <;> simp [h]` from Core.lean's existing simp set.
No additions to Core needed.

| Pattern | Proof | Sketch occurrences |
|---------|-------|--------------------|
| `Option.map f (Option.map g v) = Option.map (f ∘ g) v` | `cases v <;> simp` | 11 (7 sketches) |
| `Option.map id v = v` | `cases v <;> simp` | 2 |
| `Option.map f (Option.map f v) = v` given `∀ a, f (f a) = a` | `cases v <;> simp [h]` | 6 (5 sketches) |

These sketch theorems are redundant — they restate what Core already
derives. Trimming them is the first measured compression of the sketches.

### Sketch trimming results (2026-04-16)

| Sketch | Before | After | Removed | Reduction |
|--------|--------|-------|---------|-----------|
| CategoryTheory | 94 | 61 | 33 | 35% |
| FieldTheory | 95 | 63 | 32 | 34% |
| Analysis | 144 | 100 | 44 | 31% |
| GroupTheory | 121 | 102 | 19 | 16% |
| Algebra | 129 | 100 | 29 | 22% |
| Combinatorics | 105 | 88 | 17 | 16% |
| Geometry2 | 152 | 139 | 13 | 9% |
| Topology | 139 | 130 | 9 | 6% |
| LinearAlgebra2 | 122 | 114 | 8 | 7% |
| NumberTheory | 113 | 109 | 4 | 4% |
| InformationTheory2 | 81 | 76 | 5 | 6% |
| MeasureTheory2 | 98 | 94 | 4 | 4% |
| Data | 182 | 179 | 3 | 2% |
| RingTheory2 | 147 | 147 | 0 | 0% |
| **Total** | **1,722** | **1,502** | **220** | **13%** |

## The DRY Axis — Independent of Zero-Management (2026-04-16)

Tested on Combinatorics: 108 files, 28,401 lines, 2,824 genuine
declarations. **ZERO dissolved declarations** — no zero-management
infrastructure at all. Pure math.

Sketch: `Origin/Combinatorics.lean` — 88 lines.
Reduction: 28,401 → 88 lines (99.7%).

This reduction comes entirely from DRY:

```
Layer 1 — Trivial proofs:       180 declarations (6.4% of genuine)
  rfl:            117
  Iff.rfl:         14
  by simp:         40
  by rfl/norm_num:  9

Layer 2 — Tactic verbosity:
  rw uses:        1,503 (dominant tactic)
  Multi-line rw:    417 chains with 3+ rewrites
  omega:             47 (underused — should replace many rw chains)
  ring:              38 (underused)
  decide:             6 (underused)

Layer 3 — Specialization:
  foo_nat/int/real:   2 (minimal in this domain)
```

**What this proves:** the DRY axis is real and independent of the 17
typeclasses. Even in a domain with zero zero-management, Origin
achieves 99.7% reduction. The two axes — zero-management dissolution
AND global DRY optimization — are not additive. They're
multiplicative. Every domain gets both.

The global optimizer has never run on Mathlib. Origin is that
optimizer.

## Active Patterns

### 1. `core_trivial_proof` (Layer 1)

**What it detects:** Declarations whose entire proof is `rfl`, `Iff.rfl`,
`by simp`, `by rfl`, `by trivial`, `by exact <term>`, or `by norm_num`.

**Why it's safe:** Core.lean's instances and `@[simp]` lemmas already
derive these. Keeping them verbatim is duplication.

**What it produces:** Nothing (declaration deleted).

**Numbers (2026-04-15):**
- Matched: 21,649 / 160,525 genuine declarations (13.5%)
- Breakdown: 14,601 `rfl`, 1,253 `Iff.rfl`, 1,251 `by simp`, 170 `by rfl`, 42 `by norm_num`
- Line savings: ~49,000 lines (pending dependency-guarded run)

**Dependency guard finding (2026-04-16):**
Layer 1 yields ~3% actual deletions after the dependency guard.
Tested on Mathlib_CategoryTheory (580 files, 11,878 genuine declarations):
- 94 `rfl` declarations without `@[simp]` (compressible candidates)
- 91 rescued by dependency guard (other proofs reference them by name)
- 3 actually deletable

Most `rfl` proofs in Mathlib are definitional unfolding lemmas — they
look trivial but other proofs `rw [foo_def]` on them. The guard
correctly rescues them. Layer 1 alone is not where the compression
lives.

**The real compression is in Layers 3-4.** The sketches already proved
this: GroupTheory 38,810 → 121 lines wasn't from deleting `rfl` proofs.
It was from recognizing that entire families of theorems are derivable
from Core or unnecessary when the ground is outside the domain.

## Planned Patterns

### Layer 1

**`cases_simp_lift`** — Proofs that are `by cases a <;> cases b <;> simp [h]`.
Lifting algebraic laws through Option. Core.lean's instances handle this.

**`simp_with_extras`** — Proofs that are `by simp [specific_lemma]`.
Could be `by simp` if the specific lemma is in the simp set.

### Layer 2

**`rw_then_simp`** — Proofs that `rw [a, b, c]` then `simp`. If the
rewrite targets are all `@[simp]` lemmas, one `simp [a, b, c]` suffices.

**`omega_replacement`** — Multi-step `linarith` + `ring` combinations
on naturals/integers that `omega` closes in one step.

**`decide_replacement`** — Finite propositions with `Decidable` instances
where `decide` closes the goal directly.

**`hypothesis_strip`** — Declarations with `(h : x ≠ 0)` ground guards
where the proof doesn't use `h`. The hypothesis dissolves.

### Layer 3

**`specialization_collapse`** — Families of lemmas (`foo_nat`, `foo_int`,
`foo_real`) that are all instances of one generic `foo [SomeClass α]`.
Collapse to the general version.

### Layer 4

**`option_map_wrapper`** — Named wrappers around `Option.map`.
Lean's instance system makes these redundant.

## The Honest Numbers

```
Mathlib (source):           1,583,069 lines
After filter (no compress): 1,446,657 lines (8.6% reduction)
After Layer 1 (trivial):          TBD lines
After Layer 2 (tactics):          TBD lines
After Layer 3 (consolidation):    TBD lines
After Layer 4 (foundational):     TBD lines
```

Each layer's number is the proof. Lean's kernel verifies every line.
The line counts are objective. The build succeeds or it doesn't.

---

## Appendix: Language Feature References

Before writing compression patterns, you must know what both languages
can do. The script is Python. The output is Lean 4. Maximum compression
means leveraging 100% of both. The first Python app you build at age 20
is hardcoded and verbose. The one you build at 40 uses every feature
the language offers and is tiny yet powerful. We want the 40-year-old
version — for both languages.

### Python Features (the script language)

**Core:** Clean syntax, dynamic typing, REPL, 3-5x shorter than Java/C++.

**Data types:** int, float, complex, str, bool, bytes, list, tuple, set,
frozenset, dict, None, arbitrary-precision integers.

**Control flow:** if/elif/else, for, while, match/case (3.10+),
comprehensions (list, dict, set, generator).

**OOP:** Classes, single/multiple inheritance, dunder methods, @property,
@staticmethod, @classmethod, abstract base classes, @dataclass.

**Functional:** First-class functions, lambda, map/filter/reduce, closures,
higher-order functions, immutable data (tuple, frozenset).

**Modules:** import system, 200+ standard library modules, pip/PyPI
(500,000+ packages), virtual environments.

**Error handling:** try/except/else/finally, custom exceptions, context
managers (with), built-in exception hierarchy.

**Iterators & generators:** __iter__/__next__, yield, generator expressions,
itertools, lazy evaluation.

**Concurrency:** threading, multiprocessing, asyncio (async/await),
concurrent.futures, GIL removal in 3.13+.

**Metaprogramming:** Decorators, metaclasses, __getattr__/__setattr__,
type() for dynamic class creation, inspect/dir/getattr/hasattr.

**Type system:** Dynamic by default, optional type hints (PEP 484+),
typing module, Protocol for structural subtyping, mypy/pyright.

**I/O:** pathlib, os, shutil, json, csv, xml, sqlite3, struct/bytes.

**Other:** f-strings, slicing, unpacking (*rest), walrus operator (:=),
automatic GC, C extensions (ctypes/cffi/Cython), embeddable.

### Lean 4 Features (the output language)

**Every feature below is a potential compression tool.** If a Lean 4
feature can express something in fewer lines than Mathlib's current
approach, that's a compression pattern.

**Syntax:** ML-inspired, Unicode operators (∀, ∃, →, λ), unified
programs and proofs, do-notation for monadic code.

**Dependent types:** Full dependent types (the defining feature). Pi types
(∀ x : α, β x), Sigma types (Σ x : α, β x), propositions as types
(Curry-Howard), proofs as programs, universe polymorphism.

**Inductive types:** inductive for recursive data/propositions, mutual
and nested inductives, structural and well-founded recursion, auto-generated
eliminators (Rec, casesOn).

**Type classes:** class/instance for ad-hoc polymorphism. Key classes:
Functor, Monad, Applicative, BEq, Repr, ToString, Inhabited, Ord,
Hashable. Default instances, instance priorities, `deriving` for
automatic instance generation.

**Structures:** structure keyword, single/multiple inheritance via extends,
anonymous constructors, field access, where clauses.

**Theorem proving:**
- Tactic mode: intro, apply, exact, rw, simp, ring, omega, linarith,
  norm_num, decide, contradiction, induction, cases, constructor, use
- Term mode: explicit proof terms
- Mathlib: 100,000+ theorems

**Proof automation (CRITICAL for compression):**
- `simp` — simplification with lemma sets
- `decide` — decide propositions by computation
- `omega` — linear arithmetic over ℤ and ℕ
- `ring` — commutative ring identities
- `linarith` / `polyrith` — linear and polynomial arithmetic
- `aesop` — extensible proof search
- `norm_num` — numerical normalization
- `tauto` — propositional tautology checker
- Custom tactic combinators: `<;>`, `first`, `try`, `repeat`
- Tactic macros for extending the tactic language

**Metaprogramming & macros:**
- Hygienic macro system (headline Lean 4 feature)
- macro_rules for pattern-based macros
- syntax and elab for custom syntax/elaboration
- Lean 4 is its own metaprogramming language
- Custom notations via notation, infixl, infixr, prefix

**Monads & effects:** IO monad, do-notation, StateT/ReaderT/ExceptT/OptionT,
ST monad for mutable state with referential transparency.

**Quotient types:** Quotient.mk/lift/ind, Setoid class for equivalence
relations. Used for ℚ, ℝ, etc. in Mathlib.

**Attributes & pragmas:**
- `@[simp]` — mark for simp tactic
- `@[ext]` — generate extensionality lemmas
- `@[norm_cast]` — normalize coercions
- `@[reducible]` / `@[semireducible]` / `@[irreducible]` — control unfolding
- `@[inline]` / `@[specialize]` — compiler hints
- `@[derive]` — auto-derive instances
- `@[aesop]` — register for aesop

**Performance:** Compiled to native code via C backend, reference counting,
functional but in-place (FBIP), @[extern] for C FFI, unsafe escape hatch.

**Key insight for compression:** Lean 4's most powerful features —
`aesop`, `decide`, `omega`, `deriving`, custom tactic macros — are
barely used in Mathlib (see tactic profile above). The gap between
what Lean 4 CAN do and what Mathlib DOES is where compression lives.
