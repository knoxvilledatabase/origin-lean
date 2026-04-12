# Class Architecture: Inheritance-Based Foundation

## The Insight

Math is built on top of itself starting at arithmetic. The class hierarchy mirrors this. Each level is a file. Each domain extends the level it needs. Laws are proved once and inherited. The DRY principle as inheritance.

## The Class Hierarchy

```
Level 0: Val α             — the type (three constructors, four rules)
Level 1: ValArith α         — raw operations (mulF, addF, negF, invF)
Level 2: ValRing α          — ring laws (assoc, comm, distrib)
Level 3: ValField α         — field laws (identity, inverse, division)
Level 4: ValOrderedField α  — ordering (le, lt, comparison)
Level 5: ValModule α β      — module/vector space (scalar action of α on β)
```

### Level 0: Val α (Foundation.lean)

The type itself. Three constructors. Sort dispatch via `@[simp]`.

```lean
inductive Val (α : Type u) where
  | origin : Val α
  | container : α → Val α
  | contents : α → Val α
```

No class needed. This is the root. Everything uses this type.

**Also contains:** `valMap`, `valPair`, sort predicates, injectivity, `contents_ne_origin`, `contents_congr`. The universal infrastructure that every level uses.

### Level 1: ValArith α (Arith.lean)

The raw operations. No laws yet — just the functions.

```lean
class ValArith (α : Type u) where
  mulF : α → α → α
  addF : α → α → α
  negF : α → α
  invF : α → α
```

**Operations defined here:** `mul`, `add`, `neg`, `inv`, `fdiv`
**Simp lemmas:** all constructor combinations for each operation
**No algebraic laws.** This level only says "α has these operations."

**Domains at this level:**
- SetTheory (ordinal arithmetic is just raw operations)
- Computability (evaluation is raw computation)
- Logic (no algebraic laws needed)
- Data/Nat, Data/List (raw operations on data structures)

### Level 2: ValRing α (Ring.lean)

Ring laws. Extends ValArith.

```lean
class ValRing (α : Type u) extends ValArith α where
  mul_assoc : ∀ a b c, mulF (mulF a b) c = mulF a (mulF b c)
  add_assoc : ∀ a b c, addF (addF a b) c = addF a (addF b c)
  mul_comm : ∀ a b, mulF a b = mulF b a
  add_comm : ∀ a b, addF a b = addF b a
  left_distrib : ∀ a b c, mulF a (addF b c) = addF (mulF a b) (mulF a c)
  right_distrib : ∀ a b c, mulF (addF a b) c = addF (mulF a c) (mulF b c)
  neg_mul : ∀ a b, mulF (negF a) b = negF (mulF a b)
  mul_neg : ∀ a b, mulF a (negF b) = negF (mulF a b)
  neg_neg : ∀ a, negF (negF a) = a
```

**Lifted laws proved here:** `val_mul_assoc`, `val_add_assoc`, `val_mul_comm`, `val_add_comm`, `val_left_distrib`, `val_right_distrib`, `val_neg_mul`, `val_mul_neg`, `val_neg_neg`, `val_sub_mul`, `val_mul_sub`

**Domains at this level:**
- GroupTheory (group = ring without additive structure, but ring subsumes)
- RepresentationTheory (representations are ring homomorphisms)
- CategoryTheory/Preadditive (bilinear composition = ring distributivity)
- HomologicalAlgebra (chain complexes over rings)
- RingTheory (the study of rings themselves)
- Combinatorics (generating functions, incidence algebra)
- NumberTheory/ArithmeticFunctions (Dirichlet convolution ring)

### Level 3: ValField α (Field.lean)

Field laws. Extends ValRing.

```lean
class ValField (α : Type u) extends ValRing α where
  one : α
  zero : α
  mul_one : ∀ a, mulF a one = a
  one_mul : ∀ a, mulF one a = a
  add_zero : ∀ a, addF a zero = a
  zero_add : ∀ a, addF zero a = a
  mul_inv : ∀ a, mulF a (invF a) = one
  add_neg : ∀ a, addF a (negF a) = zero
```

**Lifted laws proved here:** `val_mul_one`, `val_one_mul`, `val_add_zero`, `val_zero_add`, `val_mul_inv`, `val_inv_mul`, `val_add_neg`, `val_neg_add`, `val_fdiv` laws

**Domains at this level:**
- FieldTheory (Galois theory, splitting fields)
- LinearAlgebra (needs field for scalar division)
- NumberTheory (needs field for fractions, p-adic, L-series)
- AlgebraicGeometry (schemes over fields)
- Probability (expectation, conditional probability need division)

### Level 4: ValOrderedField α (OrderedField.lean)

Ordering. Extends ValField.

```lean
class ValOrderedField (α : Type u) extends ValField α where
  leF : α → α → Prop
  le_refl : ∀ a, leF a a
  le_trans : ∀ a b c, leF a b → leF b c → leF a c
  le_antisymm : ∀ a b, leF a b → leF b a → a = b
  le_total : ∀ a b, leF a b ∨ leF b a
  add_le_add : ∀ a b c, leF a b → leF (addF a c) (addF b c)
  mul_pos : ∀ a b, leF zero a → leF zero b → leF zero (mulF a b)
```

**Lifted laws proved here:** `val_le` ordering on Val, comparison through contents, absolute value, min/max

**Domains at this level:**
- Analysis (limits, convergence, derivatives — all need ordering)
- Topology (ordering induces topology)
- MeasureTheory (measures are ordered, integration needs comparison)
- FunctionalAnalysis (norms are ordered)
- Geometry (distances, angles need ordering)
- Dynamics (entropy, Birkhoff averages need ordering)
- InformationTheory (KL divergence, entropy need ordering)

### Level 5: ValModule α β (Module.lean)

Module/vector space structure. Two-type class.

```lean
class ValModule (α β : Type u) [ValField α] [ValArith β] where
  smulF : α → β → β
  smul_assoc : ∀ (r s : α) (v : β), smulF r (smulF s v) = smulF (ValArith.mulF r s) v
  smul_add : ∀ (r : α) (u v : β), smulF r (ValArith.addF u v) = ValArith.addF (smulF r u) (smulF r v)
  add_smul : ∀ (r s : α) (v : β), smulF (ValArith.addF r s) v = ValArith.addF (smulF r v) (smulF s v)
  one_smul : ∀ v : β, smulF ValField.one v = v
```

**Lifted laws proved here:** `val_smul` on Val β, scalar multiplication dispatch, module axioms lifted

**Domains at this level:**
- LinearAlgebra (vector spaces, matrices, eigenvalues)
- FunctionalAnalysis (Banach/Hilbert spaces)
- RepresentationTheory (group representations as module actions)
- DifferentialGeometry (tangent spaces as modules)

## Domain-to-Level Map

| Domain | Level | Imports | Why this level |
|---|---|---|---|
| **SetTheory** | 1 (ValArith) | Foundation + Arith | Ordinal ops are raw arithmetic |
| **Computability** | 1 (ValArith) | Foundation + Arith | Computation is raw evaluation |
| **Logic** | 0 (Val) | Foundation only | Pure propositional/predicate structure |
| **Data** | 1 (ValArith) | Foundation + Arith | Data structure operations |
| **GroupTheory** | 2 (ValRing) | + Ring | Group = ring structure on operations |
| **RepresentationTheory** | 2+5 (ValRing + ValModule) | + Ring + Module | Representations are module actions |
| **CategoryTheory** | 2 (ValRing) | + Ring | Preadditive = bilinear = ring |
| **HomologicalAlgebra** | 2 (ValRing) | + Ring | Chain complexes over rings |
| **Combinatorics** | 2 (ValRing) | + Ring | Generating functions, incidence algebra |
| **RingTheory** | 2 (ValRing) | + Ring | The study of rings |
| **FieldTheory** | 3 (ValField) | + Field | Galois theory needs division |
| **NumberTheory** | 3 (ValField) | + Field | Fractions, p-adic, L-series |
| **LinearAlgebra** | 3+5 (ValField + ValModule) | + Field + Module | Vector spaces need scalar field |
| **AlgebraicGeometry** | 3 (ValField) | + Field | Schemes over fields |
| **Probability** | 3 (ValField) | + Field | Expectation needs division |
| **Analysis** | 4 (ValOrderedField) | + OrderedField | Limits need ordering |
| **Topology** | 4 (ValOrderedField) | + OrderedField | Order topology |
| **MeasureTheory** | 4 (ValOrderedField) | + OrderedField | Measures need comparison |
| **FunctionalAnalysis** | 4+5 (ValOrderedField + ValModule) | + OrderedField + Module | Norms + vector structure |
| **Geometry** | 4 (ValOrderedField) | + OrderedField | Distances, angles |
| **Dynamics** | 4 (ValOrderedField) | + OrderedField | Entropy, Birkhoff averages |
| **InformationTheory** | 4 (ValOrderedField) | + OrderedField | KL divergence, entropy |
| **Condensed** | 2 (ValRing) | + Ring | Pure categorical, uses preadditive |
| **ModelTheory** | 1 (ValArith) | Foundation + Arith | First-order structures |

## File Structure

```
ValClass/
  Foundation.lean           — Val α type, valMap, sort predicates, @[simp] dispatch
  Arith.lean                — ValArith class, operations (mul, add, neg, inv)
  Ring.lean                 — ValRing extends ValArith, lifted ring laws
  Field.lean                — ValField extends ValRing, identity/inverse laws
  OrderedField.lean         — ValOrderedField extends ValField, ordering laws
  Module.lean               — ValModule class, scalar action laws

  -- Level 1 domains (import Arith):
  SetTheory.lean
  Computability.lean
  ModelTheory.lean
  Data.lean
  Logic.lean

  -- Level 2 domains (import Ring):
  GroupTheory.lean
  RepTheory.lean
  CategoryTheory.lean
  HomologicalAlgebra.lean
  Combinatorics.lean
  RingTheory.lean
  Condensed.lean

  -- Level 3 domains (import Field):
  FieldTheory.lean
  NumberTheory.lean
  LinearAlgebra.lean
  AlgebraicGeometry.lean
  Probability.lean

  -- Level 4 domains (import OrderedField):
  Analysis.lean
  Topology.lean
  MeasureTheory.lean
  FunctionalAnalysis.lean
  Geometry.lean
  Dynamics.lean
  InformationTheory.lean
```

**~30 files. Each domain file imports exactly one level file. Max depth: 2 reads (level file + domain file). Foundation + level file = the complete context for any domain.**

## Import Chain

```
Foundation.lean (root)
  └── Arith.lean (Level 1)
       ├── Ring.lean (Level 2)
       │    ├── Field.lean (Level 3)
       │    │    ├── OrderedField.lean (Level 4)
       │    │    │    └── Module.lean (Level 5)
       │    │    │
       │    │    ├── FieldTheory.lean
       │    │    ├── NumberTheory.lean
       │    │    ├── LinearAlgebra.lean (+ Module)
       │    │    ├── AlgebraicGeometry.lean
       │    │    └── Probability.lean
       │    │
       │    ├── GroupTheory.lean
       │    ├── RepTheory.lean (+ Module)
       │    ├── CategoryTheory.lean
       │    ├── HomologicalAlgebra.lean
       │    ├── Combinatorics.lean
       │    ├── RingTheory.lean
       │    └── Condensed.lean
       │
       ├── SetTheory.lean
       ├── Computability.lean
       ├── ModelTheory.lean
       ├── Data.lean
       └── Logic.lean

OrderedField.lean
  ├── Analysis.lean
  ├── Topology.lean
  ├── MeasureTheory.lean
  ├── FunctionalAnalysis.lean (+ Module)
  ├── Geometry.lean
  ├── Dynamics.lean
  └── InformationTheory.lean
```

**No circular dependencies. No diamond inheritance. Single inheritance chain at the core (ValArith → ValRing → ValField → ValOrderedField). ValModule is a separate branch for two-type structure.**

## Why This Reduces Lines

### 1. Inheritance eliminates parameter passing

Old: every theorem carries `(mulF : α → α → α) (h_assoc : ∀ a b c, ...) (h_comm : ∀ a b, ...)`
New: every theorem carries `[ValRing α]`

Savings: ~2-4 lines per theorem × 56,815 theorems = **~113,000-227,000 lines saved**

### 2. Shared base classes eliminate duplication

GroupTheory and RepresentationTheory both need ring laws. Old: both carry explicit parameters for the same laws. New: both say `[ValRing α]` and inherit the same proofs.

### 3. The class IS the documentation

Old: reading a theorem signature requires parsing 4 explicit parameters to understand what algebraic structure is assumed.
New: `[ValField α]` says "this is a field" immediately. The class name IS the specification.

### 4. Domain files shrink dramatically

A domain file that currently has 50 theorems each with 4 lines of parameters (200 lines of boilerplate) becomes 50 theorems with 0 lines of boilerplate. The only lines are the statement and the proof.

## The Build Plan

### Phase 1: Build the level stack (5 files)

1. **Foundation.lean** — Val type + valMap + sort predicates + simp dispatch
2. **Arith.lean** — ValArith class + operations + all constructor simp lemmas
3. **Ring.lean** — ValRing class + all lifted ring laws
4. **Field.lean** — ValField class + identity/inverse laws
5. **OrderedField.lean** — ValOrderedField class + ordering laws
6. **Module.lean** — ValModule class + scalar action laws

Each builds on the previous. Test at each level: does `by simp` still close origin cases? Does the class provide the hypotheses?

**Status:** Foundation.lean prototype complete and builds clean. Arith through Module not started.

### Phase 2: Migrate one domain as proof of concept

Pick the smallest domain (Logic: 0 B3, or InformationTheory: 41 B3) and write it on the class foundation. Compare lines vs the explicit-parameter version.

**Status:** not started

### Phase 3: Measure the savings

- Lines per B3 theorem on class foundation vs explicit foundation
- If savings confirmed, migrate all domains
- If savings not confirmed, stay with explicit approach

**Status:** not started

### Phase 4: Full migration

Migrate all 29 current files to class architecture. Domain by domain, smallest first.

**Status:** not started

### Phase 5: Continue stairs 9-19

Write the remaining B3 theorems on the class foundation. Measure convergence with the new architecture.

**Status:** not started

## The Kill Switch

If the class approach introduces diamond inheritance or typeclass resolution failures, abandon it. The explicit parameter approach works. The class approach is an optimization, not a requirement.

If `@[simp]` stops firing through class instances on any level, the architecture breaks. Test at every level.

If line savings are less than 30% compared to explicit parameters, the migration cost isn't worth it.

## The Principle

Math is built on itself. The class hierarchy mirrors how math is built. Each level adds structure. Each domain inherits what it needs. Laws are proved once and inherited forever.

The DRY principle as inheritance. The AI water consumption problem solved one class at a time.
