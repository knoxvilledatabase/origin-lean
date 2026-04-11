# Progression: Building the Foundation That Makes Everything Trivial

> **STATUS: COMPLETE.** This document is history and reference only. The foundation is built. See [PROGRESSION_STEP3.md](PROGRESSION_STEP3.md) for current work.

## The Goal

Make Foundation.lean so complete that adding a new mathematical domain is like adding a new model to a Django app. You create one file. You import Foundation. You write your domain-specific definitions. Every proof is trivial because the base handles everything. Foundation is the app. Every domain is a model.

A new domain file should look like this:

```lean
import Val.Foundation

-- Domain definition
def myDomainConcept (f : α → α → α) (x y : Val α) := ...

-- Domain theorem
theorem my_theorem (f : α → α → α) (x y : Val α) : ... := by simp
```

Import. Define. Prove with `simp`. Done.

If a domain file needs case splits on constructors, the base is incomplete. If a proof takes more than one line, the base is missing a lifted law. If you're fighting, step down and strengthen Foundation. Step back up. The proof should now be trivial.

The measure of success is not how many theorems we prove. It's how easy it is for the next person to prove the next theorem.

## Why This Compounds

When you refactor at 1% of the base, the reduction cascades upward. The further from the foundation, the more layers you pass through, the more each layer's simplification stacks on the layer below.

We saw this in origin-mathlib. Foundation.lean is 305 lines. The 87 files on top of it were 15,820 lines. We strengthened the base with simp lemmas and lifted laws. CategoryPreadditive went from 481 to 74 lines without changing the math. We didn't touch the domain file's theorems. The base got stronger. The proofs got shorter.

This is the same insight as the project itself. The ambiguity of zero at arithmetic compounds through every domain built on arithmetic. 9,682 hypotheses across 1,691 Mathlib files. Fix the ambiguity at arithmetic and the compounding works in reverse. The simplification cascades upward through every domain.

The Django mental model makes this concrete. When Django's ORM gets a new optimization, every model in every app benefits without being touched. The base got better. The models got faster. That's what Foundation.lean does for domain files. Add a simp lemma, every proof that touches that pattern gets shorter. Add a lifted law, every domain that needed that law becomes a one-liner.

The cascade:
- Proofs that were 10 lines become `by simp`
- Proofs that were `by simp` become `rfl`
- Proofs that were `rfl` were already done
- Domain files that were 200 lines become 50
- New domain files start at 50 instead of 200

The prediction: the standalone with a strong foundation will have dramatically fewer total lines than origin-mathlib's 15,343, covering the same domains. Not because we compressed the proofs. Because the foundation does the work and the domain files just declare what they are.

Every method added to the base makes every domain file shorter. Every domain file that gets shorter makes the next domain file easier to write. The foundation does more, the domains do less, the total gets leaner. The compounding never stops because every new simp lemma benefits every existing file.

## How We Got Here

The standalone came first. Three constructors, four rules, import Std, build in seconds. 509 theorems proved the concept. But it only covered foundations through commutative algebra. The question was: does this work at scale?

We went into Mathlib to find out. Built 82 files alongside Mathlib's 2.16 million lines. Every mathematical domain from arithmetic through differential geometry. 98% reduction in foundational infrastructure. 17 typeclasses dissolved. The evidence was undeniable. It works at scale.

Inside Mathlib we learned how to build this properly. Val α is an abstract base model. Foundation is the app. Every domain is a model that extends the base. Simp lemmas handle dispatch. Lifted ring laws make domain proofs one-liners. Never duplicate. Always extend. If a proof is fighting, the base is incomplete. These lessons came from building 82 files and refactoring them.

Then we tried to make the Mathlib version standalone by copying Mathlib's typeclass definitions into a Prelude.lean. It hit diamond inheritance at the arithmetic level. `CommMonoid extends Monoid` and `CommSemigroup extends Semigroup`, but `Mul` arrives from two paths. Mathlib solves this with thousands of lines of infrastructure. We'd be re-solving a problem that isn't ours.

That's when we realized: the standalone already solved it. Explicit function parameters. `def mul (f : α → α → α)`. No typeclasses. No diamonds. No infrastructure. The standalone worked from day one because it never took on Mathlib's typeclass composition problem.

The full circle: standalone (works, limited coverage) then Mathlib (works, full coverage, learned the architecture) then standalone again (works, applying everything we learned, zero dependencies).

The standalone is the future because it's the approach that was right from the beginning. We went into Mathlib to learn. We came back with the architecture. Now we apply it.

## Context for a Fresh Session

Read [CLAUDE.md](CLAUDE.md) first. Then read this.

This project has two Val stacks:

1. **`lean/OriginalArith/`** — standalone. Imports `Std` only. Builds in 4 seconds. 29 files, 6,732 lines, 509 theorems. Uses explicit function parameters (`def mul (f : α → α → α)`), no typeclasses. Covers foundations through commutative algebra.

2. **`origin-mathlib/Val/`** — inside a Mathlib fork. 82 files, 15,343 lines, ~3,000 theorems. Uses Mathlib typeclasses. Covers every domain through differential geometry. 11 typeclass instances. Abstract base model architecture. 10 Mathlib imports at the base.

The standalone is the future. origin-mathlib is the reference.

origin-mathlib proved Val α works inside the largest formal math library. That evidence is captured. The READMEs, the benchmarks, the 98% reduction — all published. But it carries Mathlib's weight: 8,246 cached files, diamond inheritance in the typeclass hierarchy, slow builds.

The standalone has none of that. Three constructors, four rules, explicit function parameters, builds in seconds. It needs to be extended to cover the same domains that origin-mathlib covers.

## What the Standalone Has

```
lean/OriginalArith/
  Foundation.lean        — Val α, three constructors, four rules, explicit (f : α → α → α)
  Algebra.lean           — faithful embedding, algebraic laws
  RingField.lean         — ring and field laws within contents
  OrderedField.lean      — ordered fields, inequalities
  VectorSpace.lean       — scalar multiplication, module laws
  PolyRing.lean          — polynomial evaluation, origin propagation
  LinearAlgebra.lean     — 2x2 determinants, Cayley-Hamilton
  Analysis.lean          — limits, convergence, indeterminate forms
  Topology.lean          — one-point compactification, origin as limit point
  Category.lean          — functor, monad, universal property
  FunctionalAnalysis.lean — norms, operators, spectral theory
  MeasureTheory.lean     — measures, null sets, Radon-Nikodym
  CommAlgebra.lean       — ideals, localization, prime ideals
  HasBoundary.lean       — one typeclass, the backwards direction
  LLVMCorrespondence.lean — formal proof that origin-llvm implements Foundation
  + 10 benchmark files
  + Domains.lean, Structure.lean, Consolidation.lean, Basic.lean
```

29 files. Builds in 4 seconds. Zero Mathlib dependency.

## What the Standalone Doesn't Have

### From the Val stack's architecture (learned in origin-mathlib):

- **`@[simp]` lemmas.** Foundation.lean has zero simp tags. The Val stack has 44. This is the single biggest improvement — adding simp to `origin_mul_left`, `contents_mul_contents`, all 9 mul combinations, all 9 add combinations, all 3 neg, all 3 inv. With simp, domain file proofs become one-liners.

- **Lifted ring laws.** The Val stack's Algebra.lean proves `right_distrib`, `left_distrib`, `neg_mul`, `mul_neg`, `sub_mul`, `mul_sub` for Val α generically. The standalone proves them per-domain or not at all. Lifting them once means every domain calls the base.

- **Abstract base model discipline.** The Val stack treats Val α as a Django abstract base model — methods on the base, domain files only extend. The standalone was written before this insight. Domain files re-prove dispatch.

- **Sort predicates.** `isOrigin`, `isContainer`, `isContents` with simp lemmas. The Val stack moved these to Foundation. The standalone doesn't have them.

### Domain coverage gaps:

The Val stack covers domains the standalone doesn't:

| Domain | Standalone | Val stack |
|---|---|---|
| Analysis deep dives (Fourier, ODE, Lp, etc.) | 1 file | 23 files |
| RingTheory (ideals, Dedekind, schemes) | 1 file | 11 files |
| Topology deep dives (metric, homotopy, sheaf) | 1 file | 9 files |
| Category deep dives (abelian, adjunction, monoidal) | 1 file | 10 files |
| LinearAlgebra deep dives (tensor, bilinear, projective) | 1 file | 8 files |
| MeasureTheory deep dives (integral, decomposition) | 1 file | 7 files |
| Probability | none | 1 file |
| Algebraic Geometry | none | 1 file |
| Differential Geometry | none | 1 file |
| Homological Algebra | none | 1 file |
| Spectral Theory | none | 1 file |
| Preadditive categories | none | 1 file |

## The Plan

### Phase 1: Strengthen Foundation.lean

Add `@[simp]` to every theorem that the Val stack tags. The goal: `simp` resolves all 9 multiplication combinations, all 9 addition combinations, all 3 negation, all 3 inverse. After this, any proof about Val α operations that only depends on sort should be closable by `simp`.

The list of simp lemmas to add (from origin-mathlib's Foundation.lean):

```
-- Origin absorption (some may already exist, just need @[simp])
@[simp] origin_mul_left, origin_mul_right
@[simp] origin_add_left, origin_add_right

-- Contents closure
@[simp] contents_mul_contents, contents_add_contents

-- Container computation
@[simp] container_mul_container, container_mul_contents, contents_mul_container
@[simp] container_add_container, container_add_contents, contents_add_container

-- Neg and Inv
@[simp] neg_origin, neg_container, neg_contents
@[simp] inv_origin, inv_container, inv_contents

-- Sort predicates
def isOrigin, def isContainer, def isContents (with @[simp] lemmas)

-- Sort disjointness
@[simp] origin_ne_container, origin_ne_contents, container_ne_contents
@[simp] contents_ne_origin, contents_ne_container
```

**Test:** Write `example : mul f origin (contents a) = origin := by simp`. If it works, Phase 1 is done.

**Build:** `lake build` in 4 seconds. Zero Mathlib.

### Phase 2: Lift Ring Laws to Algebra.lean

Prove the following for Val α generically, using explicit function parameters:

```
-- The pattern: cases a <;> cases b <;> cases c <;> simp <;> apply h
theorem val_mul_assoc (f : α → α → α) (h : ∀ a b c, f (f a b) c = f a (f b c))
    (a b c : Val α) : mul f (mul f a b) c = mul f a (mul f b c)

theorem val_left_distrib (mulF addF : α → α → α)
    (h : ∀ a b c, mulF a (addF b c) = addF (mulF a b) (mulF a c))
    (a b c : Val α) : mul mulF a (add addF b c) = add addF (mul mulF a b) (mul mulF a c)

theorem val_right_distrib (mulF addF : α → α → α)
    (h : ∀ a b c, mulF (addF a b) c = addF (mulF a c) (mulF b c))
    (a b c : Val α) : mul mulF (add addF a b) c = add addF (mul mulF a c) (mul mulF b c)

-- Similarly: val_mul_comm, val_add_assoc, val_add_comm
-- val_neg_mul, val_mul_neg, val_neg_neg
```

Each proof follows the same pattern: `cases <;> simp <;> apply h` (or `rw [h]`). The explicit function parameter approach avoids typeclasses entirely. The `h` parameter carries α's law. Val's constructors carry the sort.

**Test:** Prove `preadditive_add_comp` as a one-liner calling `val_right_distrib`. If it works, Phase 2 is done.

### Phase 3: One File Per Domain (Deep Dives)

Extend each existing domain file with the deep dives from origin-mathlib. The Val stack's domain folders have the theorems. Translate them from typeclass style to explicit parameter style.

The method for each domain:

1. Read the Val stack's domain file(s) (e.g., `origin-mathlib/Val/Analysis/*.lean`)
2. For each theorem, translate: `[Ring α]` becomes explicit `(mulF addF : α → α → α)` etc.
3. Proofs that were `simp` in the Val stack should be `simp` in the standalone (after Phase 1)
4. Proofs that called `Val.right_distrib` call `val_right_distrib` (after Phase 2)
5. Build. 4 seconds.

The order follows the tree:

1. Analysis deep dives (biggest gap: 1 file → match Val stack's 23)
2. RingTheory (1 file → match 11)
3. Topology (1 file → match 9)
4. Category (1 file → match 10)
5. LinearAlgebra (1 file → match 8)
6. MeasureTheory (1 file → match 7)
7. New domains: Probability, AlgebraicGeometry, DifferentialGeometry, HomologicalAlgebra, SpectralTheory

### Phase 4: New Domains Not in Standalone

Add domains the standalone doesn't have at all:

- Probability (from Val stack's Probability.lean)
- Algebraic Geometry (from AlgebraicGeometry.lean)
- Differential Geometry (from DifferentialGeometry.lean)
- Homological Algebra (from HomologicalAlgebra.lean)
- Spectral Theory (from SpectralTheory.lean)
- Preadditive categories (from Category/Preadditive.lean — the one-liner proof of concept)

## The Architecture Rules

These are from origin-mathlib's [CLAUDE.md](origin-mathlib/CLAUDE.md), adapted for the standalone:

### Val α is an abstract base model

Foundation.lean defines the constructors and dispatch. Algebra.lean defines the lifted laws. Every domain file calls the base. Nothing is duplicated.

### Extend, never duplicate

If you're case-splitting on constructors in a domain file, that property belongs on the base. Step down. Prove it in Foundation or Algebra. Step back up. The proof should now be trivial.

### Explicit function parameters, not typeclasses

The standalone uses `def mul (f : α → α → α)`. Not `[Mul α]`. This avoids all typeclass infrastructure — no diamonds, no resolution overhead, no Mathlib dependency. The cost: slightly more verbose signatures. The benefit: builds in 4 seconds with zero dependencies.

### One file per domain

Start with one file. Split only when the file is too large. Each file imports Foundation and/or Algebra, not sibling files. Flat imports.

### The stair rule

Build one stair at a time. If a proof is fighting, the property belongs one level lower. Step down. Strengthen the base. Step back up.

### `@[simp]` everywhere

Every theorem about Val α constructor interactions gets `@[simp]`. This is what makes domain proofs one-liners. Without simp tags, every domain re-discovers the case split. With them, `simp` handles the sort dispatch.

## Lessons Learned (from the origin-mathlib session)

These are mistakes we made and solutions we found. Read before building.

### Don't try to copy Mathlib's typeclasses

We tried creating a `Val/Prelude.lean` that defined `Semigroup`, `Monoid`, `Ring`, etc. from scratch. It hit diamond inheritance at the arithmetic level. `CommMonoid extends Monoid` and `CommSemigroup extends Semigroup`, but the `Mul` instance arrives from two paths. Mathlib solves this with thousands of lines of infrastructure. We don't need to re-solve it.

The standalone uses explicit function parameters: `def mul (f : α → α → α)`. No typeclasses. No diamonds. No infrastructure. That's the approach. Don't deviate.

### Phase 1 and 2 must be done before any domain file

We tried writing CategoryPreadditive.lean before strengthening the base with simp lemmas and lifted laws. Every proof fought. 27-case splits. `simp` not making progress. Manual constructor matching everywhere.

Then we built Stairs 1-3 (simp set, lifted laws, field laws). CategoryPreadditive became one-liner proofs. 481 Mathlib lines became 74 Val lines.

The lesson: if a domain file proof is fighting, the property belongs one level lower. ALWAYS strengthen the base first.

### The typeclass ceiling is correct

Val α is NOT a Semiring, Ring, or AddGroup. `contents(0) * origin = origin`, not `contents(0)`. Ring requires `zero_mul : 0 * a = 0` for ALL `a`. When `a` is origin, the ground absorbs.

This is the sort doing its job. Don't try to register Ring on Val α. Don't create a ValContents sub-type to work around it. The ring lives inside contents. The sort lives outside. They don't need to be unified.

In the standalone, this isn't even an issue because there are no typeclass instances. The lifted laws are just theorems with explicit parameters.

### The proof pattern

Every lifted law follows the same proof:

```lean
theorem val_right_distrib (mulF addF : α → α → α)
    (h : ∀ a b c, mulF (addF a b) c = addF (mulF a c) (mulF b c))
    (a b c : Val α) : mul mulF (add addF a b) c = add addF (mul mulF a c) (mul mulF b c) := by
  cases a <;> cases b <;> cases c <;> simp <;> apply h
```

Origin cases: `simp` closes them (Foundation's simp lemmas handle origin absorption).
Non-origin cases: `simp` reduces to `constructor(expression) = constructor(expression)`. Then `apply h` (or `rw [h]`) applies α's law inside the constructor.

If this pattern doesn't work, Foundation is missing a simp lemma. Step down. Add the lemma. Step back up.

### What `simp` does here

Without Mathlib, there is no Mathlib simp set. The only simp lemmas are the ones we tag in Foundation.lean. If Foundation has zero `@[simp]` tags (the current state), `simp` does nothing. Phase 1 is entirely about adding these tags. Without Phase 1, nothing else works.

After Phase 1, `simp` knows:
- `mul f origin x = origin` (for any x)
- `mul f x origin = origin` (for any x)
- `mul f (contents a) (contents b) = contents (f a b)`
- `mul f (container a) (container b) = container (f a b)`
- `mul f (container a) (contents b) = container (f a b)`
- `mul f (contents a) (container b) = container (f a b)`
- Same for `add`, `neg`, `inv`
- `isOrigin origin = True`, `isOrigin (contents a) = False`, etc.

That's 40+ lemmas. Each one is `@[simp] theorem name := rfl` or `@[simp] theorem name := by cases x <;> rfl`. Trivial to add. Critical to have.

### The `_root_` prefix

When Val α has a theorem named `mul_assoc` and you also want to reference α's `mul_assoc` (from the hypothesis `h`), Lean may report ambiguity. Use `_root_.mul_assoc` for α's version. This comes up in every lifted law proof. Expect it.

In the standalone with explicit parameters, this is less of an issue because α's laws come through the `h` parameter, not through a typeclass name.

### The honest answer about Mathlib

The standalone needs zero Mathlib. But it also has no typeclass instances. You pass functions explicitly everywhere. If you want `mul_assoc` to be available automatically on Val α without passing it, you need typeclass instances. If you want typeclass instances, you need Mathlib's typeclass definitions. That's a different path.

The standalone path: explicit parameters, zero Mathlib, builds in seconds, slightly more verbose.
The origin-mathlib path: typeclasses, 10 Mathlib imports, builds in tens of seconds, less verbose.

The PROGRESSION chooses the standalone path. Don't mix them.

### x/y=z is one bucket divided by one bucket equals one bucket

Every value sits in a bucket. `contents(x) / contents(y) = contents(x/y)`. The bucket is transparent. The arithmetic inside contents IS α's arithmetic. The bucket doesn't interfere.

`contents(0) * contents(5) = contents(0)` is arithmetic. Zero apples. Still apples.
`origin * contents(5) = origin` is absorption. The ground took it.

Same result in traditional math. Different sorts here. This distinction is the entire project. Every proof, every lemma, every file exists because of this distinction.

## The Kill Switch

If something becomes more complex than the explicit parameter approach, we missed something at the foundation level. The standalone should be simpler than origin-mathlib at every level because it has no typeclass overhead, no Mathlib dependency, and no diamond inheritance.

If it's not simpler, step down.

If a proof is fighting, the property belongs one level lower. If a domain file needs case splits, the base is missing a lemma or a lifted law. Fix the base. The domain proof should then be trivial.

## The Reference

origin-mathlib's Val stack is the reference implementation. Every theorem in the standalone should have a counterpart there. The Val stack proves it works inside Mathlib. The standalone proves it works without Mathlib.

Key files in origin-mathlib for reference:

- `origin-mathlib/Val/Foundation.lean` — 44 simp lemmas, sort predicates. Copy the simp tags.
- `origin-mathlib/Val/Algebra.lean` — lifted ring laws. Translate to explicit parameters.
- `origin-mathlib/Val/Field.lean` — inverse, division, dissolved hypotheses.
- `origin-mathlib/Val/Category/Preadditive.lean` — the 481 to 74 line test case. Every theorem a one-liner.
- `origin-mathlib/Val/CLAUDE.md` — the abstract base model architecture.
- `origin-mathlib/Val/PROGRESSION.md` — what was done and what remains.

## Build and Verify

```bash
cd lean
lake build    # should take ~4 seconds
```

Zero sorries. Zero Mathlib. Zero typeclasses from the 17. Builds in seconds.
