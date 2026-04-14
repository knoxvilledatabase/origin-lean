# origin-lean

A proof of concept for the unification of undefined and indeterminate behaviors across mathematics, logic, physics and computation. 

---

## What this is

This proof of concept built on one observation: the symbol 0 carries two meanings that were never separated.

**contents(0)** — we counted and found nothing. A measurement result. A quantity. Zero apples in the hand.

**origin** — the ground the counting stands on. Not a quantity. Not a measurement. The precondition for counting to exist. The ground the hand rests on.

Every formal system that represents both as `0 : α` must rebuild the distinction from scratch — using hypotheses, typeclasses, conventions, or restrictions. Mathlib uses 17 typeclasses and 9,682 `≠ 0` hypotheses. Physics carries `h : r ≠ 0` and `h : T > 0` and `h : ψ ∈ domain(A)`. Logic carries `h : φ is well-formed` and restricts self-reference through hierarchies.

Three constructors separate what was conflated:

```
inductive Val (α : Type u) where
  | origin    : Val α           -- the ground. not a quantity.
  | container : α → Val α       -- the hand. last known value.
  | contents  : α → Val α       -- the apple. the count.
```

The sort dispatch asks once. The answer is in the constructor. The hypothesis doesn't exist.

## The three layers

### [Mathematics](MATHEMATICS_README.md)

173,646 Mathlib theorems classified by structure: 51.9% structural plumbing, 15.4% zero-management, 32.7% domain-specific mathematics. The classification was done by representative sampling and structural reasoning, not theorem-by-theorem. Exhaustive classification is in progress (see [PROGRESSION_STEP4.md](PROGRESSION_STEP4.md)).

| | Mathlib | origin-lean |
|---|---|---|
| Foundation typeclasses | 17 (zero-management) | 5 (single inheritance) |
| `≠ 0` hypotheses | ~9,700 (grep count) | 0 |
| Foundation lines | ~2,160,000 | 10,756 |

origin-lean restates the **foundation** — the type, the operations, the algebraic laws, and the domain-level patterns. It does not restate all 56,815 genuinely-new (B3) theorems. Those are each written once at the general level; the specific cases are instances. The domain-specific mathematics has not yet been fully restated on the Val foundation.

The claim: **the sort carries what the 17 typeclasses guarded.** The algebraic infrastructure — simp lemmas, coercion wrappers, typeclass instances — should be absorbed by the sort dispatch. The analytic engine — convergence, completeness, compactness — stays as hypotheses. This is being tested domain-by-domain through exhaustive classification.

### [Physics](PHYSICS_README.md)

86 existence hypotheses dissolved across every major domain of physics. Eight physically distinct kinds of existence boundary — spanning four centuries of physics — dissolve through the same constructor.

| Boundary | Domain | What Val replaces |
|---|---|---|
| Spatial singularity | Classical EM, GR | `h : r ≠ 0` |
| Particle vacuum | QFT | `h : state ≠ vacuum` |
| Thermal boundary | Thermodynamics | `h : T > 0` |
| Field singularity | Electromagnetism | `h : field defined` |
| Operator domain | Quantum mechanics | `h : ψ ∈ domain(A)` |
| Phase transition | Statistical mechanics | `h : ordered phase` |
| Event horizon | General relativity | Coordinate vs physical singularity |
| Renormalization | Quantum field theory | `h : renormalized` |

Two mechanisms work together: **Val's sort dispatch handles existence** (does this quantity exist here?). **Lean's type system handles kind** (what kind of counting is this? — dimensional analysis). Combined: zero existence hypotheses and zero dimensional hypotheses.

The physics layer extends the math foundation with `liftBin₂` for cross-type operations (mass × acceleration = force) and five-dimensional unit analysis (mass, length, time, temperature, current).

### [Logic](LOGIC_README.md)

12 well-formedness hypotheses dissolved. The Liar, Russell, and Curry paradoxes unified under one theorem.

```lean
theorem no_contents_fixed_point
    (f : α → α) (hf : ∀ a : α, f a ≠ a)
    (v : Val α) (hv : valMap f v = v) : v = origin
```

If a function has no fixed point on α, then no contents value is a fixed point of `valMap f` on `Val α`. The Liar asks for `v = ¬v`. Russell asks for `R ∈ R ↔ R ∉ R`. Curry asks for `C = (C → False)`. All three are the same impossibility: a formal system trying to hold its own ground.

Origin satisfies these equations vacuously — but origin is not a truth value. It's the ground truth values stand on. The paradoxes don't "evaluate to origin." They ask for contents answers that can't exist. The sort makes visible why.

**The honest boundary:** Val names why the paradoxes arise. It does not resolve them. Gödel's incompleteness, the halting problem, and proof theory remain as they are. The contribution is structural: the sort makes certain confusions visible as type-level impossibilities rather than semantic paradoxes.

## The pattern across domains

| Domain | What dissolves | Count |
|---|---|---|
| Mathematics | `≠ 0` hypotheses, 17 typeclasses | ~9,700 |
| Physics | Existence hypotheses (8 boundary types) | 86 |
| Logic | Well-formedness hypotheses, paradox structure | 12 |

The numbers differ in scale because mathematics refactored 2.1 million existing lines, physics built 3,000 lines from scratch, and logic built 718 lines proving structural results. The comparison is mechanism, not magnitude: all three dissolve their domain's hypotheses through the same constructor and the same proof pattern.

**Same constructor. Same sort dispatch. Same proof pattern.** The sort carries what the hypotheses guarded — in every domain.

## The shepherd

A shepherd holds an apple. He eats the apple. Now his hand has no apples.

The shepherd knew three things without naming them:

- **The ground** he stands on. He didn't make it. He can't hold it. It was there before him.
- **The hand** itself. One hand. Whether holding an apple or not.
- **The apple**, or the absence of an apple. The quantity.

The shepherd never confused these. He never tried to hold the ground. He knew holding was something that happens *on* the ground.

When Brahmagupta formalized zero in 628 CE, the ground and the empty hand and the absent apple entered mathematics as one symbol. The ground became a quantity. The quantity became the ground. Every formal system built on that arithmetic inherited the confusion — and built its own patch independently.

Mathlib's 17 typeclasses. Physics' `h : r ≠ 0`. Tarski's hierarchy. Renormalization. NaN. `Option<T>`. 97 patches across four fields. Each one a different community discovering that they tried to hold the ground and it didn't work.

The sort system doesn't make holding the ground possible. It makes the impossibility visible at the type level — so you stop trying.

The shepherd always knew. Now there's a type that says why.

## The file structure

```
Val/
  Foundation.lean          — Level 0: Val type, valMap, sort dispatch
  Arith.lean               — Level 1: ValArith class, operations
  Ring.lean                — Level 2: ValRing, lifted ring laws
  Field.lean               — Level 3: ValField, identity/inverse
  OrderedField.lean        — Level 4: ordering
  Module.lean              — Level 5: scalar action

  [14 mathematics domain files — see MATHEMATICS_README.md]

  Physics/
    Singularity.lean       — Core patterns: liftBin₂, inverse-square law
    Dimension.lean         — Type-level dimensional analysis (5 base units)
    Classical.lean         — Newtonian mechanics
    Thermodynamics.lean    — Laws, absolute zero as origin
    Electromagnetism.lean  — Maxwell, Lorentz force, monopole
    QuantumMechanics.lean  — Observables, uncertainty, measurement
    StatMech.lean          — Partition functions, phase transitions
    Relativity.lean        — Spacetime, event horizons
    FieldTheory.lean       — QFT, renormalization boundaries

  Logic/
    WellFormedness.lean    — Core: no_contents_fixed_point theorem
    Paradox.lean           — Liar, Russell, Curry, Tarski hierarchy

  Demo/
    PointCharge.lean       — Existence boundary test: singularities (passed)
    Vacuum.lean            — Existence boundary test: vacuum state (passed)
    Logic.lean             — Well-formedness test: Liar fixed point (passed)
    Compute.lean           — Concrete values: 2+3=5, ring laws on Int/Bool/String
    [5 math challenge files — see MATHEMATICS_README.md]
```

```bash
git clone https://github.com/knoxvilledatabase/origin-lean.git
cd origin-lean
lake build Val.Logic.Paradox          # logic layer
lake build Val.Physics.FieldTheory    # physics layer
lake build Val.Demo.Compute           # math demos
```

## How to break this

The kill switch is live at every level. See [FALSIFICATION.md](https://github.com/knoxvilledatabase/original-arithmetic/blob/main/FALSIFICATION.md).

Or: find a theorem that requires one of the 17 typeclasses and cannot be restated with Val α. The mathematics domains tested so far are the 13 exhaustively classified in [THEOREM_MAP.md](THEOREM_MAP.md) plus Order (in progress). Find a physics existence boundary that origin doesn't handle. Find a contents value that is a fixed point of negation on Bool. One example kills the claim.

If it breaks, we want to know. If it breaks, that's information.

## Where this came from

The three constructors and four rules are formally verified in [original-arithmetic](https://github.com/knoxvilledatabase/original-arithmetic) (509 Lean 4 theorems). The philosophy, the formal argument, and the 97-patch table are there.

This repository is the scaled proof: every domain of mathematics, every domain of physics, and the structural logic of self-reference. Built from the same seed. Three constructors. Four rules.

*509 theorems. Zero errors. Zero sorries.*
*— Lean 4, 2026 CE*
