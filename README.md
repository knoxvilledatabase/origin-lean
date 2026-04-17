# Welcome to Origin!

If you want to see what happens when the absolute rigor of pure mathematics meets the uncompromising logic of computer science, look no further than [Mathlib](https://github.com/leanprover-community/mathlib4). It isn't just a library; it's a monumental, community-driven effort to digitize the sum of human mathematical knowledge within the Lean theorem prover. Mathlib is widely considered the "gold standard" for formalized mathematics.

While studying Mathlib's 2.16 million lines, we noticed a pattern. Zero is confusing.  

Not only is zero treated as a quantity, it's also treated as the ground the thinker about the numbers stands on.  

**The challenge:** prove the foundational laws of algebra, order, metric spaces, functors, topology, measure theory, logic, and physics without any of the 17 zero-management Mathlib typeclasses.

**The theorem:**

```
Step 1: Write origin as a cancellation.
        origin = b - b

Step 2: Multiply both sides by n.
        n × origin = n × (b - b)

Step 3: Apply the distributive property.
        n × (b - b) = nb - nb

Step 4: A number minus itself cancels.
        nb - nb = origin

Therefore: n × origin = origin
```

Here's our proof:

```
origin.lean     338 lines    zero sorries
```

```bash
git clone https://github.com/knoxvilledatabase/origin-lean.git
cd origin-lean
lake build
```

---


## The Proofs


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
