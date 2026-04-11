# What Comes Next

## Where We Are

19 files. 2,611 lines. 19 domains. Builds in under 1 second. Zero Mathlib. Zero typeclasses.

```
Val/
  Foundation.lean           (217)  — the app. simp set. dispatch. sort predicates.
  Algebra.lean              (198)  — lifted ring laws. every domain calls this.
  RingField.lean            (104)  — inverse, division, dissolved hypotheses.
  OrderedField.lean         (130)  — ordering within contents. comparison implies contents.
  VectorSpace.lean          (115)  — scalar multiplication, module laws.
  PolyRing.lean             (129)  — polynomial evaluation, Horner, origin propagation.
  FunctionalAnalysis.lean   (137)  — norms, operators, spectral theory basics.
  SpectralTheory.lean       (110)  — spectrum, resolvent, spectral radius.
  Probability.lean          (130)  — random variables, expectation, variance.
  AlgebraicGeometry.lean    (139)  — Spec, Zariski, schemes.
  DifferentialGeometry.lean (151)  — tangent vectors, forms, connections.
  HomologicalAlgebra.lean   (134)  — chain complexes, exact sequences, homology.
  Analysis/Core.lean        (128)  — limits, convergence, indeterminate forms dissolve.
  Topology/Core.lean        (139)  — compactification, origin as limit point.
  Category/Core.lean        (129)  — valMap, functor, monad, universal property.
  Category/Preadditive.lean (109)  — the test case. every theorem a one-liner.
  LinearAlgebra/Core.lean   (131)  — 2x2 det, Cramer, Cayley-Hamilton.
  MeasureTheory/Core.lean   (135)  — measures, null sets, Radon-Nikodym.
  RingTheory/Core.lean      (146)  — ideals, localization, prime ideals.
```

Every proof is `rfl`, `by simp`, or a one-liner calling Algebra. The foundation does the work.

## The Path Forward

### 1. Deep Dives

Each domain has a Core.lean with foundations and key results. The origin-mathlib Val stack had deep dives for each domain:

| Domain | Core (done) | Deep dives (origin-mathlib had) |
|---|---|---|
| Analysis | 1 file | 22 files (Fourier, ODE, Lp, Complex, Convex, etc.) |
| RingTheory | 1 file | 10 files (Dedekind, Noetherian, Schemes, etc.) |
| Topology | 1 file | 8 files (Metric, Homotopy, Sheaf, etc.) |
| Category | 2 files | 8 files (Abelian, Monoidal, Adjunction, etc.) |
| LinearAlgebra | 1 file | 7 files (Tensor, Bilinear, Projective, etc.) |
| MeasureTheory | 1 file | 6 files (Integral, Decomposition, etc.) |

Each deep dive is a new file in the domain folder. Import Core.lean. Write domain-specific definitions and theorems. Every proof calls the base. 80-150 lines each.

**Method:** Read the origin-mathlib reference file. Translate from typeclass style to explicit parameters. Build. If a proof fights, the base is missing something. Step down.

**Start with:** Analysis deep dives. Biggest coverage gap. Each one is independent (Fourier doesn't need ODE, Convex doesn't need Lp).

### 2. Benchmarks

The old standalone had 10 benchmark files comparing Val against standard approaches:

- NeZeroBenchmark — 5 hypotheses dissolved
- InvBenchmark — convention dissolved
- ZeroDivBenchmark — NoZeroDivisors dissolved
- ZModBenchmark — 8 hypotheses dissolved
- ContainerBenchmark — MulZeroClass split
- AddBenchmark — addition trade-off
- CramerBenchmark — 8 hypotheses to 0, every proof rfl
- LimitBenchmark — 7 hypotheses to 0
- PolyEvalBenchmark — 6 hypotheses to 0
- DivisionRingBenchmark — 7 hypotheses to 0

These go in Val/Benchmarks/. Each one shows a specific dissolution: the standard approach with its hypotheses, then the Val approach without them.

### 3. HasBoundary — The Backwards Direction

The old standalone had HasBoundary.lean — one typeclass, two axioms:

```lean
class HasBoundary (α : Type) [Mul α] where
  boundary : α
  absorbs_left : ∀ a, boundary * a = boundary
  absorbs_right : ∀ a, a * boundary = boundary
```

This is the backwards direction: start from Mathlib's structures, show they consolidate into one typeclass. Port it.

### 4. LLVMCorrespondence

The formal proof that origin-llvm implements Foundation.lean. Every pass action mapped to a Foundation theorem. Zero sorries. Port it — the Foundation definitions are the same.

### 5. README

origin-lean doesn't have a README yet. It needs:

- What this is (one line)
- `lake build` (one command)
- The 19 files and what they cover
- Link to original-arithmetic for the philosophy
- Link to origin-mathlib for the Mathlib evidence
- Link to origin-ir for the compiler

### 6. Make It a Real Library

Someone should be able to add origin-lean as a dependency:

```lean
-- In their lakefile.lean
require «origin-lean» from git "https://github.com/knoxvilledatabase/origin-lean"

-- In their code
import Val.Foundation

def myTheorem : ... := by simp
```

The lakefile and lean-toolchain are already set up. Test it by creating a separate project that imports origin-lean.

## The Order

1. README (makes the repo usable)
2. Benchmarks (makes the evidence concrete)
3. HasBoundary (completes the backwards direction)
4. LLVMCorrespondence (connects to the compiler stack)
5. Deep dives (extends coverage)
6. Library packaging (makes it importable)

Each one is independent. Do them in any order. The foundation is done.

## The Principle

If adding a deep dive file takes more than 150 lines, the base is missing something. Step down. Strengthen Foundation or Algebra. Step back up.

If a proof takes more than one line, the base is missing a simp lemma or a lifted law. Step down. Add it. Step back up.

The measure of success is not how many files we add. It's how easy each file is to add. The foundation should make the next file trivial.

`lake build` in under 1 second. Always.
