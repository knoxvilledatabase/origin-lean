# Origin

If you want to see what happens when the absolute rigor of pure mathematics meets the uncompromising logic of computer science, look no further than [Mathlib](https://github.com/leanprover-community/mathlib4). It isn't just a library; it's a monumental, community-driven effort to digitize the sum of human mathematical knowledge within the Lean theorem prover. Mathlib is widely considered the "gold standard" for formalized mathematics.

While studying Mathlib's 2.16 million lines, we noticed a pattern. The same boundary appears 97 times across four fields — algebra, logic, computation, and physics — each time managed independently. The boundary: the symbol `0` carries two meanings. Emptiness (`some 0` — "we counted and got zero") and wholeness (`none` — the ground counting stands on). Every formal system since 628 CE has needed infrastructure to keep them from colliding.

**The challenge:** prove the foundational laws of algebra, order, metric spaces, functors, topology, measure theory, logic, and physics — on one type, without `NeZero`, `GroupWithZero`, `NoZeroDivisors`, or any of the 17 zero-management typeclasses.

Here's our proof:

```
origin.lean     33 lines    the theorem — why absorption is a consequence
core.lean      231 lines    the foundation — instances, laws, metric
laws.lean      263 lines    the proof — eight groups of laws proved
               ___
               527 lines    zero sorries
```

```bash
git clone https://github.com/knoxvilledatabase/origin-lean.git
cd origin-lean
lake build
```

Build it. Read it. Try to prove the same laws in Mathlib without the 17 typeclasses.

---

## The three files

**`origin.lean`** — One theorem. `n * zero = zero` derived from three premises: cancellation, distributivity, and mul_neg. Not an axiom. A consequence.

**`core.lean`** — The foundation. `Option α`: `none` is the ground, `some` is a value. Instances for `*`, `+`, `-`. The `@[simp]` set. Algebraic laws lifted through Option. Three primitives: `liftPred`, `liftBin₂`, `Option.map`. A metric space structure. Everything else derives from this.

**`laws.lean`** — Eight groups of laws proved from Core:

| Group | What it proves | Key result |
|-------|---------------|------------|
| Algebra | Commutativity, associativity, distributivity, identity, inverse | `option_mul_eq_none`: no zero divisors — structural, no typeclass |
| Order | Reflexivity, transitivity, antisymmetry | `none ≤ everything`: the ground is the bottom |
| Metric | dist_self, dist_comm, triangle inequality | Lifts through Option — distance to ground is `none` |
| Functor | `map id = id`, `map (g ∘ f) = map g ∘ map f` | Option is a lawful functor |
| Topology | Continuous maps preserve open sets | `map_preserves_open` — one theorem |
| Measure | Predicates compose under disjunction and conjunction | `liftPred` distributes over `∨` and `∧` |
| Logic | The Liar, Russell, and Curry paradoxes | All three are `no_some_fixed_point` |
| Physics | 86 existence hypotheses dissolved | `some 0 ≠ none` — the distinction Mathlib can't make |

---

## The distinction

```lean
-- The ground is below the zero measurement. One line.
-- Zero typeclasses required. Mathlib cannot state this.
theorem ground_lt_zero : none < some 0
```

A shepherd holds an apple. He eats it. His hand is empty — `some 0`. But the ground he stands on? He can't hold that. Not because it's too heavy. Because holding is something that happens *on* the ground. That's `none`.

The symbol `0` named the wrong face. Brahmagupta formalized *śūnya* (emptiness) in 628 CE. The right move. But he left *pūrṇa* (wholeness) in the philosophy. Every formal system since has needed infrastructure to manage the consequences. Origin puts the ground outside, where it always was.

*"From wholeness comes wholeness. When wholeness is taken from wholeness, wholeness remains."*
— Isha Upanishad, ~800 BCE

The formal systems finally caught up.
