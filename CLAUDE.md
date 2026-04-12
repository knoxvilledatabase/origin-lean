# For AI Agents

**Read this first. Then build.**

---

## What This Project Is

A standalone Lean 4 library that restates mathematics through three constructors (origin, container, contents) and five inheritance levels instead of Mathlib's 17 zero-management typeclasses. Zero Mathlib dependency. Builds in under 1 second.

**20 files. 10,781 lines. Every domain in Mathlib. 99.5% reduction.**

## How to Build

```bash
cd origin-lean
lake build    # <1 second
```

## How to Understand the Codebase

Read in this order:

1. **[Val/Foundation.lean](Val/Foundation.lean)** — Level 0. The type. Three constructors, valMap, sort predicates, simp dispatch. Everything starts here.

2. **[Val/Arith.lean](Val/Arith.lean)** — Level 1. ValArith class. Operations (mul, add, neg, inv) with all simp lemmas.

3. **[Val/Ring.lean](Val/Ring.lean)** — Level 2. ValRing class. Lifted ring laws (associativity, commutativity, distributivity). The proof pattern: `cases <;> simp [op, Law]`.

4. **Any domain file** — pick one. Every theorem uses `[ValRing α]` or `[ValField α]`. 2 reads (level file + domain file) gives full context.

5. **[README.md](README.md)** — the big picture, the numbers, the exhaustive mapping.

6. **[CLASS_ARCHITECTURE.md](CLASS_ARCHITECTURE.md)** — the 5-level design, domain-to-level mapping.

## The Architecture

Five levels of inheritance. Single chain. No diamonds.

```
Level 0: Val α               — Foundation.lean (type + valMap + sort dispatch)
Level 1: ValArith α           — Arith.lean (operations + simp)
Level 2: ValRing α            — Ring.lean (ring laws)
Level 3: ValField α           — Field.lean (identity + inverse)
Level 4: ValOrderedField α    — OrderedField.lean (ordering)
Level 5: ValModule α β        — Module.lean (scalar action)
```

Every domain extends the level it needs:
- `[ValArith α]`: SetTheory, Computability, Data, Logic
- `[ValRing α]`: GroupTheory, CategoryTheory, Combinatorics, RingTheory
- `[ValField α]`: FieldTheory, NumberTheory, LinearAlgebra, Geometry
- `[ValOrderedField α]`: Analysis, Topology, MeasureTheory, InformationTheory

## Key Rules

### The class carries the algebra. The simp set carries the dispatch.

```lean
-- The class provides the hypothesis:
theorem val_mul_assoc [ValRing α] (a b c : Val α) :
    mul (mul a b) c = mul a (mul b c) := by
  cases a <;> cases b <;> cases c <;> simp [mul, ValRing.mul_assoc]
```

### Never duplicate

Every line must produce behavior no other line already produces. If `by simp` closes it, the theorem doesn't exist. Run `./scripts/audit.sh` after every change.

### Strip until it hurts

If your solution feels robust and "properly engineered" — you haven't stripped enough. The discomfort of "too simple" is the signal you're on the right path.

## How to Add a Domain

```lean
import Val.Ring  -- or Val.Field, Val.OrderedField — the level you need

namespace Val
universe u
variable {α : Type u}

-- Define domain concepts
structure MyStructure (α : Type u) where
  someField : α → α

-- Prove domain theorems using class
theorem my_theorem [ValRing α] (s : MyStructure α) (a b : α) :
    mul (contents a) (contents b) ≠ origin := by simp

end Val
```

Import the level. Define. `by simp`. Done.

## Build and Verify

```bash
lake build           # builds all 20 files in <1 second
./scripts/audit.sh   # checks for duplication
```

Zero sorries. Zero Mathlib. 5 typeclasses (single inheritance). Builds in seconds.
