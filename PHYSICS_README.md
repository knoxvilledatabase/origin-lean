# Physics Layer

86 existence hypotheses dissolved across every major domain of physics. Same constructor. Same sort dispatch. Same proof pattern. 11 files. 3,000 lines. Zero errors. Zero sorries.

---

The math layer asked: what if we eliminated the infrastructure at arithmetic? 9,682 `≠ 0` hypotheses dissolved. 17 typeclasses made redundant. The sort carries what the hypotheses guarded.

The physics layer asks a different question: does the same mechanism handle existence boundaries in physics?

The answer is yes. Eight physically distinct kinds of existence boundary — spanning four centuries of physics and seven research communities — dissolve through the same constructor that handles zero-management in mathematics.

## The existence boundaries

| Boundary | Physical meaning | Standard approach | Val approach |
|---|---|---|---|
| **Spatial singularity** | Field undefined at r=0 | `h : r ≠ 0` threaded everywhere | `origin` absorbs. No hypothesis. |
| **Particle vacuum** | No particles to count | `h : state ≠ vacuum` | `origin`. Not "zero particles." |
| **Thermal boundary** | Temperature doesn't apply | `h : T > 0` | `origin`. Third law is structural. |
| **Field singularity** | E or B undefined at a point | `h : field defined` | `origin` per field. Independent. |
| **Operator domain** | State not in domain(A) | `h : ψ ∈ domain(A)` | `origin`. Sort carries domain. |
| **Phase transition** | Order parameter doesn't exist | `h : ordered phase` | `origin`. Not "zero magnetization." |
| **Ergodicity breaking** | Time average undefined | `h : ergodic` | `origin`. Process-dependent. |
| **Renormalization** | Quantity doesn't exist until renormalized | `h : renormalized` | `origin`. Bare ≠ contents. |

Each row is a different physical concept of "this quantity doesn't exist here." Each was historically handled by its own community with its own patch. One constructor handles all of them.

## The critical distinctions

**contents(0) ≠ origin.** This is the physics layer's core contribution, stated three ways:

- `contents(0)` = "we measured and found zero." A measurement result. The quantity exists.
- `origin` = "we're not in a region where this quantity applies." Not a measurement.
- The standard symbol 0 conflates both. The sort separates them.

**Coordinate singularity ≠ physical singularity.** Relativity.lean demonstrates the most important version: the event horizon is `contents` in Kruskal coordinates (crossable, the metric exists) but appears singular in Schwarzschild coordinates. The physical singularity at r=0 is `origin` in all coordinate systems. Origin is coordinate-invariant. Contents(0) is coordinate-dependent. That's physically correct.

**The magnetic monopole.** `magneticChargeDensity = origin` by construction. Not a hypothesis. Not a convention. A structural fact carried by the sort. In a universe with monopoles, you'd change origin to contents. This is origin carrying a physics assumption about the universe — deeper than any previous use.

**The uncertainty principle.** `ΔA · ΔB` where either observable is undefined on the state: the product is origin. Not a large number. Not infinity. The question doesn't apply. The `≥ ℏ/2` bound is a property of contents values. The existence question is handled before arithmetic begins.

## The numbers

| File | Lines | Boundary type | Hypotheses dissolved |
|---|---|---|---|
| Demo/PointCharge.lean | 227 | Spatial singularity | 14 |
| Demo/Vacuum.lean | 299 | Particle vacuum | 17 |
| Physics/Singularity.lean | 136 | Core patterns | — |
| Physics/Dimension.lean | 205 | Type engineering | — |
| Physics/Classical.lean | 280 | Mechanical singularity | 5 |
| Physics/Thermodynamics.lean | 363 | Thermal boundary | 9 |
| Physics/Electromagnetism.lean | 304 | Field singularity | 6 |
| Physics/QuantumMechanics.lean | 311 | Operator domain | 14 |
| Physics/StatMech.lean | 316 | Phase/thermal/ergodic | 9 |
| Physics/Relativity.lean | 281 | Event horizon | 4 |
| Physics/FieldTheory.lean | 278 | Renormalization | 8 |
| **Total** | **3,000** | | **86** |

```bash
git clone https://github.com/knoxvilledatabase/origin-lean.git
cd origin-lean
lake build Val.Physics.Classical   # or any file
```

## The two-mechanism architecture

The physics layer uses two mechanisms. Each does what it's best at. Neither overreaches.

**Val's sort dispatch handles existence.** Singularities, vacua, undefined limits, operator domains, phase boundaries, bare quantities. The question: does this quantity exist here? Origin absorbs. No hypothesis.

**Lean's type system handles kind.** Dimensional analysis — force + velocity doesn't compile. Mass × acceleration = force verified by `rfl`. Five base dimensions (mass, length, time, temperature, current). The question: what kind of counting is this? The type prevents dimensional errors at compile time.

Combined: zero dimensional hypotheses AND zero existence hypotheses. Two mechanisms. Each doing what it's best at.

```lean
-- Newton's second law: F = ma
-- Dimensional consistency: Lean's type system. No hypothesis.
-- Existence boundary: Val's sort dispatch. No hypothesis.
def newtonForce [ValArith α]
    (mass : Val (Quantity Dim.M α))
    (accel : Val (Quantity Dim.acceleration α)) :
    Val (Quantity Dim.force α) :=
  mulQ mass accel
```

## What the foundation provides

**`liftBin₂`** — the genuinely new thing for physics. Math's `mul` and `add` are same-type: `Val α → Val α → Val α`. Physics needs cross-type: `Val α → Val β → Val γ`. Mass × acceleration = force. Charge × electric field = force. Different dimensions in, different dimension out. Origin absorption works identically across types.

**Five-level dimensional analysis.** `Dim` as exponent vectors with five base units. Dimensional arithmetic is exponent addition. All verified by `rfl`:

```
M × acceleration = force          ✓
charge × electricField = force     ✓
entropy × temperature = energy     ✓
permittivity × E² = energyDensity ✓
```

**The inverse-square law pattern.** `invSquare k r`: the k/r² pattern that appears in Coulomb, gravity, and radiation. Origin at the singularity. Contents elsewhere. Proved once, used in every domain file that has a 1/r² law.

## The honest boundary

**Val handles the existence structure.** The algebraic relationships between physical quantities. Whether a quantity exists at a given point, in a given state, at a given scale. 86 hypotheses dissolved.

**Val does NOT handle the analytic engine:**
- Differential geometry — curl, divergence, Einstein field equations
- PDE existence/uniqueness — wave equations, heat equations
- Hilbert space completeness — spectral theorem for unbounded operators
- Thermodynamic limit — N → ∞, V → ∞
- Path integral construction — the foundation of QFT
- Renormalization group machinery — asymptotic freedom, BPHZ

These stay as hypotheses. The same boundary as the math layer: algebra handled, analysis deferred. Nothing overclaimed.

**Three things Val explicitly does not resolve:**
- **The measurement problem** (QM) — Val names where the boundary is but doesn't resolve it
- **Quantum gravity** (GR) — Val names the singularity but nobody knows what's on the other side
- **The renormalization problem** (QFT) — Val names bare vs renormalized but the machinery is deferred

These are open problems in physics. They stay open. The file names them honestly before building, not after.

## The proof pattern

Every theorem follows the same pattern. Every file. Every domain. No exceptions.

```lean
theorem some_physics_result [ValArith α] (x : Val α) (y : Val α) :
    physicsFunction x origin = origin := by
  simp [physicsFunction]           -- or: cases x <;> simp [...]
```

`cases <;> simp` closes everything. Origin absorbs. Contents computes. The sort dispatch asks once. The answer is in the constructor. The hypothesis doesn't exist.

## The connection to the math layer

The physics layer extends the same foundation that handles mathematics:

| | Math layer | Physics layer |
|---|---|---|
| Foundation | Val α, three constructors | Same + liftBin₂, Dim, Quantity |
| What dissolves | `≠ 0` hypotheses | Existence hypotheses |
| Count | 9,682 (Mathlib) | 86 (this library) |
| Domains | 14 mathematical | 7 physical |
| Proof pattern | `cases <;> simp` | `cases <;> simp` |
| Honest boundary | Analytic engine deferred | Analytic engine deferred |

The numbers differ in scale because the math layer refactored 2.1 million existing lines while the physics layer is a new library built from scratch. The comparison is mechanism, not magnitude: both dissolve their domain's existence hypotheses through the same constructor and the same proof pattern.

## Where this came from

The three constructors and four rules are formally verified in [original-arithmetic](https://github.com/knoxvilledatabase/original-arithmetic) (509 Lean 4 theorems). The math layer is [origin-lean](https://github.com/knoxvilledatabase/origin-lean) (10,756 lines, every Mathlib domain). The physics layer builds on both.

The demos came first. PointCharge.lean tested whether origin handles physical singularities. Vacuum.lean tested whether it handles quantum existence boundaries. Both passed. Only then were the domain files built. Test before committing. The kill switch was live at every step.

## How this was built

Human-AI collaboration. The human held the architecture — the philosophical distinction between existence and kind, the decision that Val handles existence and types handle kind, the build order from confirmed demos to domain files. AI built the implementation, stress-tested every design decision, and caught the wrong approach (using origin for dimensional mismatch) before it was committed.

The most important decision was the one NOT made: the initial design used origin for dimensional mismatch (force + velocity = origin). The human-AI loop caught that this corrupts origin's meaning — a force exists, it's just the wrong kind. That distinction (existence vs kind) became the two-mechanism architecture. The wrong version was never built.
