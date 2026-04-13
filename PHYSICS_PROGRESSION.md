# Physics Layer: Progression

## What Justified This

`Val/Demo/PointCharge.lean` tested whether the Val foundation handles physical singularities the way it handles mathematical zero-boundary conditions. The answer: yes. 14 hypotheses dissolved across 12 theorems. The mechanism is identical.

The key finding: **N singularities in a system require zero hypotheses and N independent sort dispatches.** Two point charges don't need two `r ≠ 0` guards with careful threading. They're two independent sort dispatches that each handle themselves. The composition is free. This is the same structural property that made the math layer work.

## The Philosophical Clarification

During design of the physics layer, a critical distinction emerged:

**Val handles existence. Types handle kind.**

- **Origin** = the ground the counting stands on. Not a quantity. Not a degenerate value. Categorically prior to counting.
- **Contents** = a quantity exists and can be counted. Zero is a count. contents(0) is a measurement result.
- **Container** = a quantity was here, its last known count is preserved.

This means:
- **Singularities: Val's domain.** At r=0, the field doesn't exist. Not a weird value, not infinity — no value. That's origin. The sort dispatch handles it.
- **Dimensional analysis: NOT Val's domain.** A force and a velocity both exist. They're both counts. They're counts of different *kinds* of things. That difference belongs in Lean's type system, not in Val's sort dispatch.

Using `origin` for dimensional mismatch would corrupt the meaning of origin. A force is a count. It exists. Saying "force + velocity = origin" would mean "this quantity doesn't exist" — but it does exist, it's just the wrong kind. That's a type error, not an existence boundary.

**Val does one thing and does it exactly right. That's stronger than Val doing two things with the second one being slightly wrong.**

## What to Build

### Two separate mechanisms, honest about what each does:

**1. Dimensional analysis — Lean's type system (Approach A)**

```lean
structure Quantity (d : Dim) (α : Type) where val : α
-- Val (Quantity Force ℝ) and Val (Quantity Velocity ℝ) are different types
-- force + velocity doesn't typecheck — Lean catches it, not Val
```

This is clean type engineering. Val adds nothing here. Lean's type system is the right tool. Build `Val/Physics/Dimension.lean` as type infrastructure, not as a Val contribution.

**2. Existence boundaries — Val's sort dispatch**

Where Val genuinely contributes to physics:
- **Singularities** — field doesn't exist at r=0 (demonstrated in PointCharge.lean)
- **Vacuum states** — field doesn't exist in vacuum (origin, not contents(0))
- **Undefined limits** — quantity doesn't exist at this boundary
- **Renormalization divergences** — quantity literally isn't defined until renormalized
- **Phase transitions** — order parameter doesn't exist in the disordered phase
- **Event horizons** — information doesn't exist beyond the horizon

These are all existence questions, not kind questions. Val handles them.

### Build order:

```
Val/Physics/
  Dimension.lean         — type system for units (NOT a Val contribution — clean engineering)
  Singularity.lean       — Val's contribution: existence boundaries in physics
  Classical.lean         — Newtonian mechanics (singularities + dimensions)
  Thermodynamics.lean    — laws, absolute zero as origin
  Electromagnetism.lean  — Maxwell's equations, field singularities
  QuantumMechanics.lean  — Hilbert space, vacuum as origin
  StatMech.lean          — partition functions, phase transitions
  Relativity.lean        — spacetime, event horizons as origin
  FieldTheory.lean       — QFT, renormalization boundaries
```

Dimension.lean is type engineering. Singularity.lean is Val's contribution. Both come before domain files. Each domain file uses both mechanisms.

### The demo sequence:

1. **Already done:** `Val/Demo/PointCharge.lean` — singularity dissolution (passed)
2. **Next:** `Val/Demo/Dimension.lean` — type-level dimensional analysis (Approach A, not Val dispatch)
3. **Then:** `Val/Demo/Vacuum.lean` — vacuum state as origin (Val's contribution)
4. If all three pass: build the infrastructure files

## What NOT to Do

1. **Don't use origin for dimensional mismatch.** That corrupts the meaning of origin. Dimensions are about kind, not existence. Use Lean's type system.

2. **Don't overclaim Val's contribution to physics.** Val handles existence boundaries (singularities, vacua, undefined limits). It does NOT handle dimensional analysis, approximation, or empirical constants. State this from day one.

3. **Don't confuse type-checking with proving.** Same lesson as math. The algebraic structure flows from the foundation. The analytic engine (PDEs, convergence, completeness) remains hypothesis territory.

4. **Test before committing.** Demo each mechanism independently before building domain files.

## The Honest Boundary (Stated Up Front)

**Val handles:**
- Singularity dissolution — origin absorbs, no hypothesis threading
- Vacuum states — origin represents genuine absence
- Existence boundaries — where quantities become undefined

**Lean's type system handles:**
- Dimensional analysis — incompatible types don't compile
- Unit conversion — type-level algebra on dimensions

**Neither handles (hypothesis territory):**
- PDE existence/uniqueness
- Approximation and limits
- Empirical validation
- Renormalization (the full machinery, not just the boundary)

Two mechanisms. Each doing what it's best at. Honest about both.

## Where to Start

1. Read `Val/Demo/PointCharge.lean` — the existence test that passed
2. Read `Val/Foundation.lean` through `Val/OrderedField.lean` — the 5-level stack
3. Build `Val/Demo/Dimension.lean` — type-level dimensional analysis (Approach A)
4. Build `Val/Demo/Vacuum.lean` — vacuum state as origin (Val's contribution)
5. If both pass: build `Val/Physics/Dimension.lean` and `Val/Physics/Singularity.lean`
6. Then domain files, smallest first
