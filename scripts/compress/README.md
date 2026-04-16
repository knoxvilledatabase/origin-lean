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
