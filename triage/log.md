# Mathlib → Origin Triage Log

File-by-file triage against Origin/Core.lean. Method per CLAUDE.md:
grep for zero-management → classify Type A (pure math) or Type B (dissolves) → write what remains.

## Algebra/NeZero.lean (62 lines, 14 theorems)

**Type B — 100% dissolution.** Every declaration is zero-management infrastructure:
`not_neZero`, `eq_zero_or_neZero`, `zero_ne_one`, `one_ne_zero`,
`ne_zero_of_eq_one`, `two_ne_zero`, `three_ne_zero`, `four_ne_zero`,
primed variants, `NeZero.of_pos`.

All exist to manage `≠ 0` guards. With Origin, `none` is outside the counting
domain. Nothing to write. File dissolves entirely.

## Algebra/GroupWithZero/Units/Equiv.lean (73 lines, 7 theorems)

**Type B — 100% dissolution.** Every declaration requires `[GroupWithZero G₀]`
and `(ha : a ≠ 0)`: `unitsEquivNeZero`, `mulLeft₀`, `mulRight₀`,
`divRight₀`, `divLeft₀`, `mulLeft_bijective₀`, `mulRight_bijective₀`.

The entire file is permutation/bijectivity infrastructure for nonzero elements.
With Origin, multiplication by `some a` is already injective on `some` values
and `none` absorbs. Nothing to write.

## AlgebraicGeometry/EllipticCurve/IsomOfJ.lean (343 lines, 8 theorems)

**Type B — domain content, heavy threading.** The main theorem
(`exists_variableChange_of_j_eq`: elliptic curves with same j-invariant are
isomorphic over separably closed fields) is genuine algebraic geometry.
90 hits are all internal proof plumbing: `ne_zero`, `pow_ne_zero`,
`div_ne_zero_iff` threading nonzeroness of curve coefficients.
Deep domain math with full Mathlib dependency. Flag for future, skip now.

## MeasureTheory/Function/LpSeminorm/ChebyshevMarkov.lean (93 lines, 8 theorems)

**Type B — domain content, analysis boundary.** Chebyshev-Markov inequality
in Lp seminorms. The hits are `p ≠ 0`, `p ≠ ∞`, `ε ≠ 0` — measure-theoretic
boundary guards. The theorems are genuine analysis (Lp estimates, measure
bounds). This is the honest boundary: analysis infrastructure that Origin
defers as hypotheses. Domain content stays, zero-management in signatures
dissolves, but the proofs need the full Mathlib analysis stack. Skip for now.

## Data/Nat/Cast/NeZero.lean (30 lines, 4 theorems)

**Type B — 100% dissolution.** All four declarations are NeZero infrastructure
for natural number casts: `NeZero.one_le`, `natCast_ne`, `of_neZero_natCast`,
`pos_of_neZero_natCast`. Pure `≠ 0` management. Nothing to write.

## Algebra/GroupWithZero/Units/Basic.lean (531 lines, 116 theorems)

**Type B — 100% dissolution.** The entire file is `MonoidWithZero` /
`GroupWithZero` infrastructure: `Units.ne_zero`, `IsUnit.ne_zero`,
`not_isUnit_zero`, `Ring.inverse` (sends non-units to 0), and 100+
lemmas about invertibility, `≠ 0` threading, and zero-unit interactions.
`Ring.inverse` itself is the canonical example: a function that exists
because 0 is inside and needs special routing. With Origin, `none`
absorbs and units are always `some`. Nothing to write.

## FieldTheory/KummerPolynomial.lean (127 lines, 10 theorems)

**Type B — domain content, moderate threading.** Irreducibility of X^p - a.
The hits are `≠ 0` threading inside proofs: `ne_zero_of_irreducible_X_pow_sub_C`,
`root_X_pow_sub_C_ne_zero`, `C_ne_zero`, `hp.ne_zero`, `mul_ne_zero_iff`.
The main theorems (`X_pow_sub_C_irreducible_of_prime`,
`X_pow_sub_C_irreducible_iff_of_prime`) are genuine field theory with real
proof content. Deep domain math, full Mathlib dependency. Flag for future.

## Algebra/GroupWithZero/NeZero.lean (58 lines, 3 theorems)

**Type B — 100% dissolution.** `NeZero.one` (1 ≠ 0 in nontrivial monoid),
`inv_ne_zero` (a ≠ 0 → a⁻¹ ≠ 0), `inv_mul_cancel₀` (a ≠ 0 → a⁻¹ * a = 1),
`domain_nontrivial`. All GroupWithZero infrastructure. Nothing to write.

## Algebra/GroupWithZero/Conj.lean (34 lines, 2 theorems)

**Type B — 100% dissolution.** `isConj_iff₀` (conjugacy ↔ ∃ c ≠ 0, c*a*c⁻¹=b)
and `conj_pow₀` (conjugation distributes over powers, requires a ≠ 0).
Pure GroupWithZero infrastructure. Nothing to write.

## Algebra/GroupWithZero/Invertible.lean (93 lines, 11 theorems)

**Type B — 100% dissolution.** Every declaration threads `Invertible.ne_zero`
or requires `[GroupWithZero α]`: `invertibleOfNonzero`, `invOf_eq_inv`,
`inv_mul_cancel_of_invertible`, `div_mul_cancel_of_invertible`, etc.
All invertibility-meets-zero infrastructure. Nothing to write.

## Analysis/Calculus/Deriv/Inv.lean (238 lines, 36 theorems)

**Type B — analysis boundary.** Derivatives of x⁻¹ and f/g (quotient rule).
Every theorem carries `hx : x ≠ 0` or `hx : d x ≠ 0`. Genuine calculus
content. The `≠ 0` hypotheses dissolve but the analysis machinery
(HasDerivAt, DifferentiableAt) needs full Mathlib. Skip for now.

## Topology/Algebra/GroupWithZero.lean (375 lines, 52 theorems)

**Type B — 100% dissolution.** `ContinuousInv₀` typeclass: continuity of
x⁻¹ at nonzero points. Every theorem requires `GroupWithZero` + `≠ 0`.
Topological infrastructure for managing the whole being inside. Nothing to write.

## AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean (452 lines, 58 theorems)

**Type B — domain content, heavy threading.** Degree bounds on division
polynomials of elliptic curves. 76 hits, all internal `ne_zero` / `pow_ne_zero`
threading. Deep algebraic geometry, full Mathlib dependency. Flag for future.

## AlgebraicGeometry/EllipticCurve/NormalForms.lean (701 lines, 93 theorems)

**Type B — domain content, heavy threading.** Normal forms of Weierstrass
curves (short, char 2/3 forms). 116 hits threading nonzeroness of discriminants
and characteristics. Deep domain math. Flag for future.

## Analysis/Complex/CoveringMap.lean (127 lines, 11 theorems)

**Type B — analysis boundary.** Complex exponential as covering map.
Hits are `n ≠ 0`, `z ≠ 0` in complex analysis proofs. Genuine content
with full Mathlib analysis dependency. Skip for now.

## Topology/Algebra/WithZeroTopology.lean (190 lines, 18 theorems)

**Type B — 100% dissolution.** Topology on linearly ordered commutative
groups with zero. The entire file builds the topology where zero is special
(neighborhoods of zero, invertible elements are open). Pure infrastructure
for managing zero as a topological boundary. Nothing to write.

## NumberTheory/FLT/Polynomial.lean (273 lines, 13 theorems)

**Type B — domain content, moderate threading.** Mason-Stothers theorem
and polynomial FLT. 44 hits threading `≠ 0` for polynomial degrees and
coprimality. Genuine number theory. Flag for future.

## RingTheory/Valuation/ValuativeRel/Basic.lean (1367 lines, 144 theorems)

**Type B — domain content, heavy threading.** Valuative relations for
valuation rings. 216 hits — the highest raw count so far. Genuine ring theory
content with massive zero-threading. Flag for future.

## FieldTheory/RatFunc/Degree.lean (126 lines, 13 theorems)

**Type B — domain content, moderate threading.** Degree of rational functions.
20 hits threading `≠ 0` for denominators. Genuine field theory. Flag for future.

## Algebra/NoZeroSMulDivisors/Basic.lean (33 lines, 1 theorem)

**Type B — 100% dissolution.** `NoZeroSMulDivisors` lemmas — the typeclass
that says "no zero divisors in scalar multiplication." Pure infrastructure
for managing zero in module actions. Nothing to write.

## Algebra/Order/GroupWithZero/Lex.lean (135 lines, 13 theorems)

**Type B — 100% dissolution.** Lexicographic products of linearly ordered
groups with zero. All `GroupWithZero` order infrastructure. Nothing to write.

## Algebra/GroupWithZero/Action/Units.lean (128 lines, 11 theorems)

**Type B — 100% dissolution.** Multiplicative actions with zero on and by
units. Every theorem requires `GroupWithZero` or threads `≠ 0` through
scalar multiplication. Nothing to write.

## Algebra/GroupWithZero/Units/Lemmas.lean (152 lines, 15 theorems)

**Type B — 100% dissolution.** More lemmas about units in GroupWithZero.
All `≠ 0` infrastructure. Nothing to write.

## Analysis/SpecialFunctions/Sqrt.lean (167 lines, 24 theorems)

**Type B — analysis boundary.** Square root function properties. Hits are
`hx : x ≠ 0` in continuity/differentiability proofs. Genuine analysis
content with full Mathlib dependency. Skip for now.

## Algebra/Polynomial/Degree/Domain.lean (98 lines, 11 theorems)

**Type B — domain content, moderate threading.** Polynomial degree lemmas
in integral domains. 14 hits threading `≠ 0` for leading coefficients.
Some genuine content (degree of product = sum of degrees). Flag for future.

## Algebra/Module/LinearMap/DivisionRing.lean (49 lines, 4 theorems)

**Type B — 100% dissolution.** Linear maps over division rings, all
requiring `≠ 0` or `GroupWithZero`. Nothing to write.

## Data/Int/WithZero.lean (108 lines, 10 theorems)

**Type B — 100% dissolution.** `WithZero` infrastructure for integers.
Every theorem manages the adjoined zero element. Nothing to write.

## SetTheory/Ordinal/Exponential.lean (552 lines, 82 theorems)

**Type B — domain content, moderate threading.** Ordinal exponentiation.
75 hits threading `≠ 0` for ordinal arithmetic. Genuine set theory content.
Flag for future.

## Algebra/Module/Submodule/Union.lean (119 lines, 5 theorems)

**Type B — domain content, light threading.** Union of submodules directed
iff linearly ordered. 16 hits, mostly `ne_zero` in proof internals.
Some genuine module theory. Flag for future.

## RingTheory/Valuation/DiscreteValuativeRel.lean (75 lines, 2 theorems)

**Type B — domain content, moderate threading.** Discrete valuative relations.
10 hits threading `≠ 0` for valuation properties. Genuine ring theory. Flag for future.
