# origin-lean

How many lines of code does it take to do the same math as Mathlib?

Mathlib is the largest formal mathematics library ever built. 2,160,000 lines. 88,494 theorems. 8,200 files. An extraordinary achievement by a community of rigorous thinkers.

While studying it, we noticed that 53% of those theorems either exist to manage zero or are shaped by it. 17 typeclasses. 9,682 `≠ 0` hypotheses. The number zero carries 9 roles in one symbol and every domain built on arithmetic inherits the ambiguity.

We asked: what if we eliminated the ambiguity at arithmetic?

```
Arithmetic  <-- the ambiguity of zero starts here
    |
    ├── Algebra
    ├── Analysis (23 files)
    ├── LinearAlgebra (7 files)
    ├── Topology (9 files)
    ├── Category (10 files)
    ├── RingTheory (11 files)
    ├── MeasureTheory (7 files)
    ├── OrderedField
    ├── Probability
    ├── AlgebraicGeometry
    ├── DifferentialGeometry
    ├── HomologicalAlgebra
    ├── SpectralTheory
    ├── FunctionalAnalysis
    ├── VectorSpace
    └── PolyRing
```

79 files. 10,615 lines. Every domain from arithmetic through differential geometry. Builds in under 1 second. Zero Mathlib dependency. Zero typeclasses. Zero sorries.

```bash
git clone https://github.com/knoxvilledatabase/origin-lean.git
cd origin-lean
lake build
```

## How it works

Three constructors. Four rules. One pattern match before arithmetic executes.

```
match (a, b) with
| (origin, _)              => origin           -- absorption. the ground took it.
| (_, origin)              => origin           -- absorption. the ground took it.
| (container x, _)         => container x      -- propagation. last value preserved.
| (_, container y)         => container y      -- propagation. last value preserved.
| (contents x, contents y) => contents (x * y) -- arithmetic. zero apples. still apples.
```

- **origin**: nothing to retrieve. Everything downstream folds.
- **container**: the last known value is preserved. You know what you were holding.
- **contents**: safe territory. Arithmetic lives here.

The sort is resolved first. Then the arithmetic happens. The 17 typeclasses exist because a flat type system has no dispatch. The match asks once. The answer is in the constructor.

The same three sorts applied to mathematics eliminated 98% of foundational infrastructure in Mathlib. [See the evidence.](https://github.com/knoxvilledatabase/origin-mathlib4)

## The critical distinction

`contents(0) * contents(5) = contents(0)`: arithmetic. Zero is a quantity. The sort stays contents.

`origin * contents(5) = origin`: absorption. Origin is the ground. Not a quantity. Everything downstream folds.

Same result in traditional math. Different sorts here. This distinction is the entire project.

## The architecture

Foundation.lean is the app. Every domain is a model. Like a Django abstract base model, the foundation defines the dispatch and the lifted laws. Domain files import the foundation and write domain-specific definitions. Every proof is `rfl`, `by simp`, or a one-liner calling the base.

Adding a new domain:

```lean
import Val.Algebra

namespace Val
universe u
variable {α : Type u}

-- Domain definition
def myDomainConcept (f : α → α → α) (x y : Val α) := mul f x y

-- Domain theorem
theorem my_theorem (f : α → α → α) (a b : α) :
    mul f (contents a) (contents b) ≠ origin := by simp

end Val
```

Import. Define. `by simp`. Done.

If a proof takes more than one line, the foundation is missing a simp lemma. Step down. Add it. Step back up.

## The numbers

| | Mathlib | origin-lean |
|---|---|---|
| Lines | 2,160,000 | 10,615 |
| Files | 8,200 | 79 |
| Domains covered | all | 19 (foundations + deep dives) |
| Zero-management typeclasses | 17 | 0 |
| `≠ 0` hypotheses | 9,682 | 0 |
| Mathlib dependency | is Mathlib | 0 |
| Build time | minutes | <1 second |

The 10,615 lines cover the foundations and key results of every domain. The complete restatement of all 88,494 theorems is the next step. Prediction: ~23,000 lines. See [PROGRESSION_STEP3.md](PROGRESSION_STEP3.md).

## Where this came from

The three constructors and four rules are formally verified in [original-arithmetic](https://github.com/knoxvilledatabase/original-arithmetic) (509 Lean 4 theorems, zero errors, zero sorries). The philosophy: what would happen if a number wasn't allowed to also be its categorical origin?

The evidence that it works at scale: [origin-mathlib](https://github.com/knoxvilledatabase/origin-mathlib4) demonstrated Val α inside the largest formal math library. 82 files beside Mathlib's 2.16 million lines. 98% reduction in foundational infrastructure. 17 typeclasses dissolved.

origin-lean takes what was learned inside Mathlib and builds it standalone. Same architecture. Zero dependencies. Builds in seconds.

The same three sorts are consistent across the stack:
- [origin-lean](https://github.com/knoxvilledatabase/origin-lean) (this repo) — the formal proof library
- [origin-mathlib](https://github.com/knoxvilledatabase/origin-mathlib4) — the Mathlib evidence
- [origin-ir](https://github.com/knoxvilledatabase/origin-ir) — sort-native compiler IR
- [origin-lang](https://github.com/knoxvilledatabase/origin-lang) — Rust and Python runtime
- [origin-llvm](https://github.com/knoxvilledatabase/origin-llvm) — LLVM passes
- [origin-mlir](https://github.com/knoxvilledatabase/origin-mlir) — MLIR compiler passes

## How this was built

This is a Human-AI collaborated effort. The human held the concept and identified the architecture. Claude Code built the foundation, the lifted laws, and the domain files. Claude Web stress-tested every design decision. Gemini and Grok tried to pull the kill switch.

The journey: standalone (509 theorems) then Mathlib (learned the abstract base model architecture) then standalone again (applying everything learned). The full circle is documented in [PROGRESSION.md](PROGRESSION.md).

This work exists because of the timing. The concept is 2,500 years old. The formal verification tools, the AI that can implement across domains, and the adversarial loop that stress-tests every claim. A project like this was not possible before now.
