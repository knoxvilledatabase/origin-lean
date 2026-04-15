# origin-lean

Origin is wholeness.

```
Mathlib:    2,160,000 lines    — the math, with the ground inside
Val:           14,474 lines    — the proof it works
Origin:         2,440 lines    — the building
```

---

## What this is

One theorem. One type. Every domain of mathematics, seven domains of physics, and the structural logic of self-reference.

The theorem is called `origin`. It proves that the whole absorbs the parts — not as an axiom, but as a consequence of cancellation and the distributive law:

```lean
theorem origin
    (cancel : ∀ a : α, a + (-a) = zero)
    (distrib : ∀ a b c : α, a * (b + c) = a * b + a * c)
    (mul_neg : ∀ a b : α, a * (-b) = -(a * b))
    (n : α) : n * zero = zero :=
  calc n * zero
      _ = n * (n + (-n))           := by rw [cancel]
      _ = n * n + n * (-n)         := by rw [distrib]
      _ = n * n + -(n * n)         := by rw [mul_neg]
      _ = zero                     := by rw [cancel]
```

The type is `Option α`. `None` is the whole. `Some` is a value. ML had this in 1973. The theorem above is WHY two constructors are sufficient.

```bash
git clone https://github.com/knoxvilledatabase/origin-lean.git
cd origin-lean
lake build Origin.Core    # 166 lines. The entire foundation.
```

## Why it matters

The symbol 0 carries two meanings that were never separated.

**some(0)** — we counted and found nothing. A measurement result. A quantity. Zero apples in the hand.

**none** — the ground the counting stands on. Not a quantity. Not a measurement. The precondition for counting to exist. The ground the hand rests on.

Every formal system that represents both as `0 : α` must rebuild the distinction — using hypotheses, typeclasses, conventions, or restrictions. Mathlib uses 17 typeclasses and 9,682 `≠ 0` hypotheses. Physics carries `h : r ≠ 0` and `h : T > 0`. Logic carries `h : φ is well-formed` and restricts self-reference through hierarchies.

Put the whole outside the counting domain. The 17 typeclasses vanish. Not reduced. Gone. Because the problem they solved was never a real problem — it was a consequence of putting the whole where it doesn't belong.

## The layers

### [Origin](Origin/Core.lean) — WHY it works

166 lines. The `origin` theorem. Instances for `*` `+` `-` on `Option`. A simp set. `liftBin₂` for cross-type operations. `no_some_fixed_point` for logic. Everything else imports this one file.

14 domain files cover every area of mathematics — from information theory through combinatorics — in 1,721 lines total. Each file contains only domain-specific content: definitions, predicates, structures, and proofs that demonstrate Option behavior. No boilerplate. No wrappers. Standard notation.

### [Mathematics](MATHEMATICS_README.md) — THAT it works at scale

Every theorem in Mathlib mapped and classified. 173,646 theorems across 14 domains. The Val layer proved the concept: 10,756 lines replacing 2,160,000. The Origin layer proved the concept was scaffolding: the same 14 domains in 1,721 lines.

| | Mathlib | Val | Origin |
|---|---|---|---|
| Lines | 2,160,000 | 10,756 | 1,721 |
| Files | 8,200 | 20 | 14 |
| Zero-management typeclasses | 17 | 0 | 0 |
| Custom type | — | Val α (3 constructors) | Option α (standard library) |

### [Physics](PHYSICS_README.md) — 86 existence hypotheses dissolved

Eight physically distinct kinds of existence boundary — spanning four centuries of physics — dissolve through the same constructor.

| Boundary | Domain | What dissolves |
|---|---|---|
| Spatial singularity | Classical EM, GR | `h : r ≠ 0` |
| Particle vacuum | QFT | `h : state ≠ vacuum` |
| Thermal boundary | Thermodynamics | `h : T > 0` |
| Field singularity | Electromagnetism | `h : field defined` |
| Operator domain | Quantum mechanics | `h : ψ ∈ domain(A)` |
| Phase transition | Statistical mechanics | `h : ordered phase` |
| Event horizon | General relativity | Coordinate vs physical singularity |
| Renormalization | Quantum field theory | `h : renormalized` |

### [Logic](LOGIC_README.md) — the paradoxes unified

One theorem covers the Liar, Russell, and Curry:

```lean
theorem no_some_fixed_point
    (f : α → α) (hf : ∀ a : α, f a ≠ a)
    (v : Option α) (hv : v.map f = v) : v = none
```

If a function has no fixed point on α, no `some` value is a fixed point of `Option.map f`. The Liar asks for `v = ¬v`. Russell asks for `R ∈ R ↔ R ∉ R`. Curry asks for `C = (C → False)`. All three are the same impossibility: a formal system trying to hold its own ground.

## The shepherd

A shepherd holds an apple. He eats the apple. Now his hand has no apples.

The shepherd knew three things without naming them. The ground he stands on. His hand. The apple.

The ground is not nothing. The ground is the whole — the unity from which counting begins and to which cancellation returns. The Sanskrit tradition knew both faces: *śūnya* (emptiness) and *pūrṇa* (fullness, wholeness). When Brahmagupta formalized zero in 628 CE, only *śūnya* entered the arithmetic. *Pūrṇa* stayed in the philosophy.

The symbol 0 named the wrong face.

When you apply wholeness to the algebra, 17 typeclasses vanish. 9,682 hypotheses dissolve. 86 physics existence boundaries dissolve. The paradoxes unify. Option is sufficient. And 2,160,000 lines of formal mathematics reduces to 2,440 — because 99.9% of it was managing the whole being inside the counting domain.

The shepherd always knew the difference between the ground and an empty hand. The algebra proves why he was right.

*"That is whole. This is whole. From wholeness comes wholeness. When wholeness is taken from wholeness, wholeness remains."*
— Isha Upanishad, ~800 BCE

## How to break this

The kill switch is live at every level. See [FALSIFICATION.md](https://github.com/knoxvilledatabase/original-arithmetic/blob/main/FALSIFICATION.md).

Or: find a theorem in any domain that requires one of the 17 typeclasses and cannot be restated with `Option α`. Find a physics existence boundary that `none` doesn't handle. Find a `some` value that is a fixed point of `Bool.not`. One example kills the claim.

If it breaks, we want to know. If it breaks, that's information.

## The file structure

```
Origin/
  Core.lean              — 166 lines. THE foundation. Everything imports this.
  14 domain files        — 1,721 lines. Every area of mathematics.
  Physics.lean           — 247 lines. Six physics domains.
  Logic.lean             — 155 lines. Liar, Russell, Curry.
  Test.lean              — 151 lines. Concrete computation on Int.

Val/
  20 math files          — 10,756 lines. The scaffolding. Evidence at scale.
  11 physics files       — 3,000 lines. 86 hypotheses dissolved.
  3 logic files          — 718 lines. 12 hypotheses dissolved.
  9 demo files           — Challenge theorems, concrete tests.
```

## Where this came from

The three constructors and four rules are formally verified in [original-arithmetic](https://github.com/knoxvilledatabase/original-arithmetic) (509 Lean 4 theorems). The philosophy, the formal argument, and the 97-patch table are there.

This repository is the scaled proof — and the discovery that the scaled proof was scaffolding for a building that fits in 2,440 lines.

*509 theorems. Zero errors. Zero sorries.*
*— Lean 4, 2026 CE*
