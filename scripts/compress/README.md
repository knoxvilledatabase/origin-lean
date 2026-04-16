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
