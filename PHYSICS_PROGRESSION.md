# Physics Layer: Progression

## What Justified This

`Val/Demo/PointCharge.lean` tested whether the Val foundation handles physical singularities the way it handles mathematical zero-boundary conditions. The answer: yes. 14 hypotheses dissolved across 12 theorems. The mechanism is identical.

The key finding: **N singularities in a system require zero hypotheses and N independent sort dispatches.** Two point charges don't need two `r ≠ 0` guards with careful threading. They're two independent sort dispatches that each handle themselves. The composition is free. This is the same structural property that made the math layer work.

## What to Build First

**`Val/Physics/Dimension.lean`** — the dimensional analysis layer.

Make dimensional inconsistency produce `origin` the same way positional singularities produce `origin`. A force added to a velocity isn't a type error and it isn't a runtime exception — it's `origin`. Nothing to retrieve. The computation folds.

```
Val (Quantity d α)
```

Where `d` encodes the physical dimension (mass, length, time, charge...) and `α` is the numeric type. Operations between quantities of incompatible dimensions produce `origin`. The sort dispatch handles dimensional analysis the same way it handles zero management and singularities.

## What to Build After

```
Val/Physics/
  Dimension.lean         — units, dimensional analysis (THE FOUNDATION)
  Classical.lean         — Newtonian mechanics, Lagrangian, Hamiltonian
  Thermodynamics.lean    — laws, state functions, equilibrium
  Electromagnetism.lean  — Maxwell's equations, field theory
  QuantumMechanics.lean  — Hilbert space, observables, uncertainty
  StatMech.lean          — partition functions, entropy, ensembles
  Relativity.lean        — spacetime, Lorentz invariance
  FieldTheory.lean       — classical and quantum field structure
```

Dimension.lean comes first. Everything else imports it. Same pattern as Foundation.lean for math.

## What NOT to Do

The math layer taught three lessons the hard way:

1. **Don't overclaim.** The math README said "all of math" and got corrected to "algebraic skeleton with analytic hypotheses." The physics layer should say what it is from the start: structural dissolution of singularity and dimensional hypotheses, with the analytic engine (convergence, completeness, approximation) as the next frontier.

2. **Don't confuse type-checking with proving.** Hypotheses that carry the hard content are honest but they're not proofs. When the physics layer says "Maxwell's equations verified," be precise about what's verified (the algebraic structure) vs what's assumed (the PDE existence/uniqueness machinery).

3. **Test before committing.** PointCharge.lean tested the singularity hypothesis before building the physics stack. Dimension.lean should have its own demo testing dimensional dissolution before building the domain files.

## What Physics Adds That Math Doesn't

Three things the Val foundation needs to handle for physics that didn't arise in math:

1. **Empirical constants.** The speed of light, Planck's constant. Their values are measured, not proved. The foundation needs to cleanly separate structural results (hold for any `c`) from numerical results (require `c = 299,792,458 m/s`).

2. **Approximation.** Newtonian mechanics is an approximation to relativity. The ideal gas law is an approximation to stat mech. Formal verification wants exact proofs. Physics needs "true to within ε." This is genuinely hard.

3. **Models vs reality.** Formalizing "in the Standard Model" is formalizing a mathematical structure, not physical reality. The distinction matters and should be stated.

## The Honest Boundary (Stated Up Front)

The Val foundation handles:
- **Singularity dissolution** — origin absorbs, no hypothesis threading
- **Dimensional analysis** — incompatible dimensions produce origin
- **Algebraic structure** — field equations, conservation laws, symmetries

The Val foundation does NOT handle:
- **PDE existence/uniqueness** — the analytic engine
- **Approximation and limits** — convergence, completeness
- **Empirical validation** — connecting models to measurement
- **Renormalization** — the deepest physics infrastructure

Same boundary as math. Algebra trivial. Analysis hard. Honest from day one.

## Where to Start

1. Read `Val/Demo/PointCharge.lean` — the test that passed
2. Read `Val/Foundation.lean` through `Val/OrderedField.lean` — the 5-level stack
3. Build `Val/Physics/Dimension.lean` — test dimensional dissolution
4. If it works: build domain files, smallest first
5. If it doesn't: the demo told you before you built 8 files
