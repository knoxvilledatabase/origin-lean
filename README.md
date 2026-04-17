# Welcome to Origin!

[Mathlib](https://github.com/leanprover-community/mathlib4) is the largest formal mathematics library ever built. Its 2.16 million lines represent an extraordinary achievement: thousands of theorems across every major domain of mathematics, mechanically verified, contributed by a community of rigorous thinkers over years of careful work. The contributors who built Mathlib's nearly 200,000 theorems created the most rigorous work in the history of mathematics. 

While studying Mathlib's 2.16 million lines, we noticed a pattern. Zero is confusing.  

Not only is zero treated as a quantity, it's also treated as the ground the thinker about the number zero stands on.  

**The challenge:** prove the foundational laws of algebra, order, metric spaces, functors, topology, measure theory, logic, and physics without any of the Mathlib 17 zero-management typeclasses.

**What is Origin?**

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
           1 / origin = origin
```

```
origin.lean     312 lines    zero sorries
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
| Algebra | Commutativity, associativity, distributivity, identity, inverse | `none * a = none`, `none⁻¹ = none` |
| Order | Reflexivity, transitivity, antisymmetry | `none ≤ everything` |
| Metric | dist_self, dist_comm, triangle inequality | Lifts through Option, distance to ground is `none` |
| Functor | `map id = id`, `map (g ∘ f) = map g ∘ map f` | Option is a lawful functor |
| Topology | Continuous maps preserve open sets | `map_preserves_open` |
| Measure | Predicates compose under disjunction and conjunction | `liftPred` distributes over `∨` and `∧` |
| Logic | The Liar, Russell, and Curry paradoxes | `no_some_fixed_point` |
| Physics | 86 existence hypotheses dissolved | `some 0 ≠ none` |

---
