# Logic Layer

> **Note:** This documents the Val logic layer (718 lines, 3 files). The [Origin layer](Origin/Logic.lean) demonstrates the same results in 155 lines using `Option α` and `no_some_fixed_point`. Val stays as the comprehensive evidence. Origin is the foundation.

12 well-formedness hypotheses dissolved. The Liar, Russell, and Curry paradoxes unified under one theorem. 3 files. 718 lines. Zero errors. Zero sorries.

---

The math layer dissolved `≠ 0` hypotheses. The physics layer dissolved existence hypotheses. The logic layer dissolves well-formedness hypotheses — and shows why the paradoxes of self-reference can't have truth values.

The centerpiece is one theorem: **no_contents_fixed_point**. If a function `f` has no fixed point on `α`, then no contents value is a fixed point of `valMap f` on `Val α`. Origin satisfies the equation vacuously — but origin is not in the counting domain. The equation has no counting-domain answer.

The Liar, Russell, and Curry are not three separate problems. They are three notations for the same impossibility. One theorem covers all three.

## The key result

```lean
theorem no_contents_fixed_point
    (f : α → α) (hf : ∀ a : α, f a ≠ a)
    (v : Val α) (hv : valMap f v = v) : v = origin
```

If `f` has no fixed point on `α`, and `valMap f v = v`, then `v = origin`. No contents value. No container value. Only origin — the ground the counting domain stands on.

Origin satisfying the equation is not a resolution. It's the ground being the ground. Saying "origin satisfies `S = ¬S`" is like saying "the ocean satisfies the equation for fish." The ocean isn't a fish.

## The paradoxes — one impossibility, three notations

**The Liar:** "This sentence is false." Asks: is there a truth value `v` where `v = ¬v`? Bool negation has no fixed point (`!true ≠ true`, `!false ≠ false`). By `no_contents_fixed_point`: no contents value satisfies `neg v = v`. The Liar asks for a contents answer that can't exist.

```lean
theorem liar_no_contents_solution (v : Val Bool) (hv : neg v = v) :
    v = origin
```

**Russell:** `R = {x : x ∉ x}`. Is `R ∈ R`? Self-membership with negation is the same fixed-point equation: `membership(R,R) = ¬membership(R,R)`. Same theorem. Same impossibility. R was never a well-formed set — not because self-reference is prohibited (that's the patch), but because the question requires holding the ground.

```lean
theorem russell_no_contents_solution (v : Val Bool) (hv : neg v = v) :
    v = origin
```

**Curry:** "If this sentence is true, then P." When P is false, the equation `C = ¬C ∨ False` has no contents solution. The conditional self-reference can't prove false.

```lean
theorem curry_no_contents_solution (v : Val Bool)
    (hv : add (neg v) (contents false) = v) :
    v = origin
```

Three paradoxes. One theorem. The formal system tried to hold its own ground. It can't — not because origin blocks it, but because the counting domain has no value with that property.

## The framing that matters

Origin is never reached, approached, or hit. It is what the formal system stands on.

The shepherd can hold an apple. The shepherd can hold nothing (empty hand). The shepherd cannot hold the ground he stands on. Not because the ground is too heavy. Not because his hand is too small. Because holding is something that happens *on* the ground. The ground is the precondition for holding, not a thing that can be held.

Every paradox of self-reference has this structure:

- **The Liar** asks: "Can my truth value be its own negation?" — Can I hold the ground?
- **Russell** asks: "Can a set contain its own membership criterion?" — Can the fish be the ocean?
- **Curry** asks: "Can a conditional prove anything by referencing itself?" — Can a mark evaluate its own ground?
- **Gödel** asks: "Can a system prove its own consistency?" — Can the counting evaluate what makes counting possible?
- **Halting** asks: "Can a computation decide its own termination?" — Can the process contain its own precondition?

The answer is the same in every case: the question requires stepping outside the counting domain. You can't do that from inside contents. The sort makes the impossibility visible at the type level.

## Tarski's hierarchy — structural, not conventional

Why do we need Truth₀, Truth₁, Truth₂...?

Not as a patch. As a consequence.

`valMap f : Val α → Val β`. The function `f : α → β` lives *outside* Val. It operates on the contents of Val values. It cannot be a Val value itself — it's a different type. A Val value that tried to be its own evaluation function would need to be both the contents being evaluated and the function doing the evaluating — both the fish and the ocean simultaneously.

Tarski's hierarchy makes this explicit at each level. The truth predicate for level `n` lives at level `n+1`. No level evaluates itself. This isn't a restriction imposed on the system. It's what evaluation means.

## Well-formedness hypotheses dissolved

Every theorem about truth evaluation in standard logic carries `h : φ is well-formed`. In Val: the sort carries well-formedness. The hypothesis doesn't exist.

| Theorem | Standard | Val |
|---|---|---|
| eval_not_wf | h : φ wf | 0 |
| conj_left_origin | h₁ : φ wf | 0 |
| conj_right_origin | h₂ : ψ wf | 0 |
| disj_left_origin | h₁ : φ wf | 0 |
| disj_right_origin | h₂ : ψ wf | 0 |
| neg_not_wf | h : φ wf | 0 |
| pred_subject_origin | h : subject in lang | 0 |
| pred_pred_origin | h : pred in lang | 0 |
| mp_p_origin | h₁ : P wf | 0 |
| mp_imp_origin | h₂ : (P→Q) wf | 0 |
| univ_element_origin | h : x in domain | 0 |
| exist_both_origin | h : ∃ witness wf | 0 |
| **Total dissolved** | **12** | **0** |

## The honest boundary

Val names why the paradoxes arise. It does not resolve them.

The Liar paradox in full generality, Gödel's incompleteness theorems, the halting problem, and the full machinery of proof theory remain as they are. What Val contributes is structural: the sort system makes certain confusions visible as type-level impossibilities rather than semantic paradoxes.

This is narrower than what math and physics contributed. In math, 9,682 hypotheses dissolved. In physics, 86 existence hypotheses dissolved. In logic, 12 well-formedness hypotheses dissolve, and the paradoxes get structural explanations — but the paradoxes themselves are consequences of the counting domain being finite, not of a missing sort.

The contribution is precise: **the `no_contents_fixed_point` theorem shows that every self-reference paradox is the same impossibility — a formal system trying to hold its own ground.** The 97 patches in the README include 12 logic patches. Each is a different community discovering independently that they tried to hold the ground and it didn't work. The theorem names why.

## The file structure

```
Val/
  Demo/
    Logic.lean              356  — Demo: well-formedness dissolved, Liar fixed point
  Logic/
    WellFormedness.lean     137  — Core: no_contents_fixed_point, classical logic in contents
    Paradox.lean            225  — Liar, Russell, Curry, Tarski hierarchy, Gödel/halting
```

```bash
git clone https://github.com/knoxvilledatabase/origin-lean.git
cd origin-lean
lake build Val.Logic.Paradox   # builds everything
```

## The connection across domains

| Domain | What dissolves | Mechanism | Count |
|---|---|---|---|
| Mathematics | `≠ 0` hypotheses | Sort carries zero-management | 9,682 |
| Physics | Existence hypotheses | Sort carries existence | 86 |
| Logic | Well-formedness hypotheses | Sort carries well-formedness | 12 |
| Computation | Already solved | Rust `Option<T>`, ML `option` | — |

The numbers differ in scale because mathematics refactored 2.1 million existing lines, physics built 3,000 lines from scratch, and logic built 718 lines proving structural results. The comparison is mechanism, not magnitude: all three dissolve their domain's hypotheses through the same constructor and the same proof pattern.

Same constructor. Same sort dispatch. Same proof pattern. The sort carries what the hypotheses guarded — in every domain.

The shepherd always knew the difference between the ground and an empty hand. Now there's a type that says why he couldn't hold the ground.
