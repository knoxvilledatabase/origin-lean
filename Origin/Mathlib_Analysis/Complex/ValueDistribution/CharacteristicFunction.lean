/-
Extracted from Analysis/Complex/ValueDistribution/CharacteristicFunction.lean
Genuine: 1 of 2 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core

/-!
# The Characteristic Function of Value Distribution Theory

This file defines the "characteristic function" attached to a meromorphic function defined on the
complex plane.  Also known as "Nevanlinna Height", this is one of the three main functions used in
Value Distribution Theory.

The characteristic function plays a role analogous to the height function in number theory: both
measure the "complexity" of objects. For rational functions, the characteristic function grows like
the degree times the logarithm, much like the logarithmic height in number theory reflects the
degree of an algebraic number.

See Section VI.2 of [Lang, *Introduction to Complex Hyperbolic Spaces*][MR886677] or Section 1.1 of
[Noguchi-Winkelmann, *Nevanlinna Theory in Several Complex Variables and Diophantine
Approximation*][MR3156076] for a detailed discussion.

### TODO

- Characterize rational functions in terms of the growth rate of their characteristic function, as
  discussed in Theorem 2.6 on p. 170 of [Lang, *Introduction to Complex Hyperbolic
  Spaces*][MR886677].
-/

open Filter Metric Real Set

namespace ValueDistribution

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f g : ℂ → E} {a : WithTop E}

variable (f a) in

noncomputable def characteristic : ℝ → ℝ := proximity f a + logCounting f a

/-!
## Elementary Properties
-/

-- DISSOLVED: characteristic_congr_codiscrete
