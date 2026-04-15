/-
Extracted from RingTheory/MvPowerSeries/PiTopology.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-! # Product topology on multivariate power series

Let `R` be with `Semiring R` and `TopologicalSpace R`
In this file we define the topology on `MvPowerSeries σ R`
that corresponds to the simple convergence on its coefficients.
It is the coarsest topology for which all coefficient maps are continuous.

When `R` has `UniformSpace R`, we define the corresponding uniform structure.

This topology can be included by writing `open scoped MvPowerSeries.WithPiTopology`.

When the type of coefficients has the discrete topology, it corresponds to the topology defined by
[N. Bourbaki, *Algebra {II}*, Chapter 4, §4, n°2][bourbaki1981].

It is *not* the adic topology in general.

## Main results

- `MvPowerSeries.WithPiTopology.isTopologicallyNilpotent_of_constantCoeff_isNilpotent`,
  `MvPowerSeries.WithPiTopology.isTopologicallyNilpotent_of_constantCoeff_zero`: if the constant
  coefficient of `f` is nilpotent, or vanishes, then `f` is topologically nilpotent.

- `MvPowerSeries.WithPiTopology.isTopologicallyNilpotent_iff_constantCoeff_isNilpotent` :
  assuming the base ring has the discrete topology, `f` is topologically nilpotent iff the constant
  coefficient of `f` is nilpotent.

- `MvPowerSeries.WithPiTopology.hasSum_of_monomials_self` : viewed as an infinite sum, a power
  series converges to itself.

TODO: add the similar result for the series of homogeneous components.

## Instances

- If `R` is a topological (semi)ring, then so is `MvPowerSeries σ R`.
- If the topology of `R` is T0 or T2, then so is that of `MvPowerSeries σ R`.
- If `R` is a `IsUniformAddGroup`, then so is `MvPowerSeries σ R`.
- If `R` is complete, then so is `MvPowerSeries σ R`.

## Implementation Notes

In `Mathlib/RingTheory/MvPowerSeries/LinearTopology.lean`, we generalize the criterion for
topological nilpotency by proving that, if the base ring is equipped with a *linear* topology, then
a power series is topologically nilpotent if and only if its constant coefficient is.
This is lemma `MvPowerSeries.LinearTopology.isTopologicallyNilpotent_iff_constantCoeff`.

Mathematically, everything proven in this file follows from that general statement. However,
formalizing this yields a few (minor) annoyances:

- we would need to push the results in this file slightly lower in the import tree
  (likely, in a new dedicated file);
- we would have to work in `CommRing`s rather than `CommSemiring`s (this probably does not
  matter in any way though);
- because `isTopologicallyNilpotent_of_constantCoeff_isNilpotent` holds for *any* topology,
  not necessarily discrete nor linear, the proof going through the general case involves
  juggling a bit with the topologies.

Since the code duplication is rather minor (the interesting part of the proof is already extracted
as `MvPowerSeries.coeff_eq_zero_of_constantCoeff_nilpotent`), we just leave this as is for now.
But future contributors wishing to clean this up should feel free to give it a try!

-/

namespace MvPowerSeries

open Function Filter

open scoped Topology

variable {σ R : Type*}

namespace WithPiTopology

section Topology

variable [TopologicalSpace R]

variable (R) in

-- INSTANCE (free from Core): :

set_option backward.isDefEq.respectTransparency false in

theorem instTopologicalSpace_mono (σ : Type*) {R : Type*} {t u : TopologicalSpace R} (htu : t ≤ u) :
    @instTopologicalSpace σ R t ≤ @instTopologicalSpace σ R u := by
  change ⨅ i, _ ≤ ⨅ i, _
  gcongr
