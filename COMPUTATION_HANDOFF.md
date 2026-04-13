# Computation Layer — Handoff for Next Session

**Read this before touching any code.**

---

## The Parallel

The computation layer follows the same discipline as math, physics, and logic. Don't retrofit. Build it right from the start.

| | Mathematics | Physics | Logic | **Computation** |
|---|---|---|---|---|
| Clean-room build | origin-lean (.lean) | Val/Physics/ (.lean) | Val/Logic/ (.lean) | **origin-lang (.origin)** |
| Bridge/retrofit | origin-mathlib | — | — | origin-ir, origin-llvm, origin-mlir |
| Formal proof | 509 theorems | 86 hypotheses dissolved | no_contents_fixed_point | LLVMCorrespondence.lean + spec/ |
| Comparison target | Mathlib 2.1M lines | Standard physics hypotheses | Standard logic h : wf | **36 computation patches** |
| Build tool | `lake build` | `lake build` | `lake build` | **`originc` (the transpiler)** |

Origin-lang is origin-lean for computation. The IR passes are origin-mathlib — real, useful, the bridge. But the language is the clean-room build.

---

## What Already Exists

### origin-lang (`github.com/knoxvilledatabase/origin-lang`)

- **Library:** On crates.io and PyPI. Three sorts at the application layer.
- **Transpiler:** `transpiler/` — full compiler pipeline: lexer, parser, AST, emitter. Takes `.origin` files, emits Rust.
- **Spec:** `spec/` — language design document and type system specification. Every rule traces to a Lean theorem.
- **Test files:** `hello.origin`, `match_test.origin` — the first programs in the language.
- **Benchmarks:** 98.6% less energy per operation (Python → Rust).

### origin-ir, origin-llvm, origin-mlir

- Sort-aware IR layer for retrofitting existing code
- Four rules as LLVM passes (15 tests, ninja clean)
- Four rules as MLIR passes against real JAX IR
- `LLVMCorrespondence.lean` in original-arithmetic — formal proof that the LLVM pass implements Foundation.lean

### The transpiler status

The transpiler compiles. The `.origin` files parse. **The emitter output has not been verified.** The immediate technical question:

```bash
cd origin-lang/transpiler
cargo run -- ../hello.origin -o hello.rs
cat hello.rs
```

Does the emitted Rust enforce the sort semantics? Not just parse the syntax — enforce the semantics. This is the `lake build` moment for computation. Until that's verified, the language exists as spec and parser but not as enforcement.

---

## What the Computation Layer Adds That Math/Physics/Logic Didn't Need

### Origin vs Boundary

This is the most important distinction the computation layer contributes.

Math and physics mostly dealt with **origin**: the singularity, the vacuum, absolute zero. Places where the quantity doesn't exist. The ground.

Computation deals with **boundary** constantly: division by zero, overflow, null reference, hallucination. These aren't origin — the computation didn't cease to exist. It reached the edge of its domain. The shepherd's hand at the edge of the field, not the ground itself.

The origin-lang spec has this right:

- **origin** — the ground. Pure absorption. No value at all. The precondition for computation to exist.
- **boundary** — the edge. The computation reached the limit of its domain. The last known value is preserved. The reason for the boundary is named.
- **contents** — safe territory. The computation produced a value.

```origin
boundary enum InferBoundary {
    LowConfidence { confidence: f64, threshold: f64 },
    Hallucinated { claim: String, evidence_score: f64 },
    OutOfDomain { distance: f64 }
}
```

`Hallucinated` is a boundary kind, not origin. A model that hallucinates isn't in a state of non-existence. It's at the edge of its knowledge domain. `Boundary(Hallucinated, last_grounded_value)` — the last thing it knew before it crossed the edge is preserved. That's container — the hand that remembers what it held.

This maps to the three constructors:
- `origin` → `origin` (the ground, pure absorption)
- `boundary` → `container` (the hand, last known value preserved, reason named)
- `contents` → `contents` (the apple, safe arithmetic)

The language adds the **reason** — WHY the boundary was reached. Division by zero, overflow, hallucination, out of domain. The sort carries what happened. The container carries what was known. Both together give full traceability.

---

## What to Build

### 1. Verify the emitter

Run `originc` on the test files. Check that the emitted Rust:
- Represents origin as `Val::Origin`
- Represents boundary as `Val::Container` (or `Val::Boundary`) with reason and residual
- Represents contents as `Val::Contents`
- Implements the four rules: origin absorbs, boundary propagates, contents computes
- The `?` propagator correctly chains boundary/origin through operations

If the emitter works: the language is real. If not: fix the emitter before building the README.

### 2. Write the first real `.origin` program

Not a parser test. A program that actually produces boundaries:

```origin
fn divide(a: f64, b: f64) -> f64 | DivisionByZero {
    if b == 0.0 {
        boundary DivisionByZero -> a  -- boundary with residual
    } else {
        a / b
    }
}

fn pipeline(x: f64) -> f64 | DivisionByZero {
    let a = divide(x, 2.0)?    -- ? propagates boundary
    let b = divide(a, 0.0)?    -- this hits the boundary
    b                           -- never reached
}
```

This is the PointCharge.lean of computation. The first demo that confirms the mechanism works.

### 3. Build COMPUTATION_README.md

Same structure as physics and logic READMEs:
- What computation looks like from the seed
- The 36 patches mapped to what origin-lang makes structural
- The origin vs boundary distinction
- The AI safety implication (Hallucinated as a boundary kind)
- The honest boundary (what the language handles vs what it defers)
- The kill switch

The 36 patches should be a table like the physics README's existence boundary table — each patch mapped to what origin-lang replaces.

### 4. Do NOT duplicate math/physics/logic

The computation layer lives in origin-lang, not origin-lean. Origin-lean is the formal foundation. Origin-lang references it. One sentence in the README: "The formal proof that this implementation is correct lives in origin-lean."

---

## The Honest Boundary (State Before Building)

**Origin-lang handles:**
- Sort-native arithmetic (three constructors, four rules)
- Boundary types with named reasons and preserved residuals
- The `?` propagator for boundary chaining
- Compile-time sort enforcement
- The AI inference boundary (Hallucinated, LowConfidence, OutOfDomain)

**Origin-lang does NOT handle:**
- Formal verification of the emitted Rust (that's LLVMCorrespondence.lean's domain)
- Runtime performance optimization (that's origin-ir/origin-llvm)
- Hardware-level sort awareness (ISA extension, 10-year horizon)
- Whether sort-aware training actually reduces hallucination (testable hypothesis, not demonstrated)

---

## The Philosophical Framing (Do Not Lose This)

The computation patches aren't things that get "hit." DivisionByZero isn't origin. It's a boundary kind — the edge of the multiplicative domain.

The shepherd can't hold the ground. But he can stand at the edge of his field and know he's at the edge. That's boundary. Origin is the ground itself — not the fence, the earth.

A model that hallucinates isn't at origin. It's at the boundary of its knowledge. The hand was holding something. Now it's at the edge. What was it holding? The container remembers.

Origin is never reached, approached, or hit. Boundary is where the counting reaches its edge. Contents is where the counting is clean. Three sorts. The shepherd always knew all three.

---

## Files to Read First

1. `origin-lang/spec/` — language design and type system spec
2. `origin-lang/transpiler/` — the compiler pipeline
3. `origin-lang/transpiler/tests/hello.origin` and `match_test.origin`
4. `original-arithmetic/lean/OriginalArith/LLVMCorrespondence.lean` — formal proof connecting Lean to LLVM
5. This conversation's physics and logic work — for the pattern to follow
6. The CLAUDE.md in original-arithmetic — especially the communication principles

---

## The Goal

When complete, the repository map tells the full story:

| Repository | Domain | What it proves |
|---|---|---|
| origin-lean | Mathematics | 9,682 hypotheses dissolved, 17 typeclasses eliminated |
| origin-lean | Physics | 86 existence hypotheses dissolved across 8 boundary types |
| origin-lean | Logic | 12 wf hypotheses dissolved, paradoxes structurally explained |
| origin-lang | Computation | Sort-native language, 36 patches made structural |
| original-arithmetic | The seed | 509 theorems, three constructors, four rules |

Four domains. One foundation. The comparison speaks for itself.
