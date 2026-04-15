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

Cancellation returns to the ground. The distributive law propagates it through multiplication. The four-step derivation (`Origin/Foundation.lean`):

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

**Origin/** — the foundation. Option α. The absorption derivation. Physics on Option. Logic on Option. Ring and field laws lifted through two cases instead of three.

**Val/** — the evidence. The full Mathlib comparison. 14 math domains, 7 physics domains, logic paradoxes. 10,756 + 3,000 + 718 lines. Every theorem verified.

## How to Build

```bash
cd origin-lean
lake build Origin.Foundation   # the derivation
lake build Origin.Ring         # ring laws on Option
lake build Origin.Physics      # physics on Option
lake build Origin.Logic        # logic on Option
lake build Val.Demo.Compute    # Val evidence (math)
lake build Val.Physics.Classical  # Val evidence (physics)
```

## How to Understand the Codebase

Read in this order:

1. **[Origin/Foundation.lean](Origin/Foundation.lean)** — the derivation. Absorption from cancellation + distributive law. One theorem. This is WHY.

2. **[Origin/Test.lean](Origin/Test.lean)** — instantiation on Int. Option operations. Concrete computation. This is the proof it works.

3. **[Origin/Ring.lean](Origin/Ring.lean)** — ring laws lifted through Option. Two cases instead of three. 128 lines vs Val's 461.

4. **[Origin/Physics.lean](Origin/Physics.lean)** — six physics domains on Option. Same 86 hypotheses dissolved. No custom infrastructure.

5. **[Origin/Logic.lean](Origin/Logic.lean)** — `no_some_fixed_point`. Liar, Russell, Curry. Same results, one file.

6. **[Val/Foundation.lean](Val/Foundation.lean)** — the original Val type. Three constructors. The scaffolding. Read this to understand the evidence, not to build new things.

7. **[README.md](README.md)** — the big picture across all domains.

## The Architecture

**Origin (the foundation):**
```
Origin/
  Foundation.lean    — the derivation (absorption theorem)
  Test.lean          — instantiation on Int, Option operations
  Ring.lean          — ring laws on Option α
  Field.lean         — field laws on Option α
  Physics.lean       — physics on Option α
  Logic.lean         — paradoxes on Option α
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

### The class carries the algebra. The simp set carries the dispatch.

For Val:
```lean
theorem val_mul_assoc [ValRing α] (a b c : Val α) :
    mul (mul a b) c = mul a (mul b c) := by
  cases a <;> cases b <;> cases c <;> simp [mul, ValRing.mul_assoc]
```

For Origin:
```lean
theorem oMul_assoc [Mul α]
    (h : ∀ a b c : α, a * b * c = a * (b * c))
    (a b c : Option α) :
    oMul (oMul a b) c = oMul a (oMul b c) := by
  cases a <;> cases b <;> cases c <;> simp [oMul, h]
```

Same pattern. Fewer cases. No custom type.

### Never duplicate

Every line must produce behavior no other line already produces. If `by simp` closes it, the theorem doesn't exist.

### Strip until it hurts

If your solution feels robust and "properly engineered" — you haven't stripped enough. The discomfort of "too simple" is the signal you're on the right path. Origin is simpler than Val. That's the point.

## How to Add Work

New work goes in **Origin/**, not Val/:

```lean
import Origin.Ring  -- or Origin.Field

-- Use Option directly. None is the ground. Some is a value.
-- liftBin₂ for cross-type operations.
-- cases <;> simp for proofs.
```

Val/ is evidence. Don't add to it. Add to Origin/.

## Build and Verify

```bash
lake build Origin.Foundation Origin.Test Origin.Ring Origin.Field Origin.Physics Origin.Logic
```

Zero sorries. Zero Mathlib. Builds in seconds.
