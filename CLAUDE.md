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

**Origin (the foundation):**
```
Origin/
  Core.lean              — THE file. Theorem + instances + simp set. 166 lines.
  Foundation.lean        — historical: the derivation before Core existed
  Test.lean              — instantiation on Int
  Physics.lean           — physics domains on Option
  Logic.lean             — paradoxes on Option
  [domain files]         — domain content importing Core
```

**Val (the evidence):**
```
Val/
  Foundation.lean through Module.lean  — 5-level class hierarchy
  14 math domain files                 — every Mathlib domain
  Physics/                             — 7 physics domain files
  Logic/                               — paradox infrastructure
  Demo/                                — tests and challenge theorems
```

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
lake build Origin.Core    # the foundation — one file, 166 lines
```

Zero sorries. Zero Mathlib. Builds in under a second.
