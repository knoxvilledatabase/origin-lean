/-
Extracted from NumberTheory/NumberField/Units/DirichletTheorem.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Dirichlet theorem on the group of units of a number field
This file is devoted to the proof of Dirichlet unit theorem that states that the group of
units `(𝓞 K)ˣ` of units of the ring of integers `𝓞 K` of a number field `K` modulo its torsion
subgroup is a free `ℤ`-module of rank `card (InfinitePlace K) - 1`.

## Main definitions

* `NumberField.Units.rank`: the unit rank of the number field `K`.

* `NumberField.Units.fundSystem`: a fundamental system of units of `K`.

* `NumberField.Units.basisModTorsion`: a `ℤ`-basis of `(𝓞 K)ˣ ⧸ (torsion K)`
  as an additive `ℤ`-module.

## Main results

* `NumberField.Units.rank_modTorsion`: the `ℤ`-rank of `(𝓞 K)ˣ ⧸ (torsion K)` is equal to
  `card (InfinitePlace K) - 1`.

* `NumberField.Units.exist_unique_eq_mul_prod`: **Dirichlet Unit Theorem**. Any unit of `𝓞 K`
  can be written uniquely as the product of a root of unity and powers of the units of the
  fundamental system `fundSystem`.

## Tags
number field, units, Dirichlet unit theorem
-/

noncomputable section

open Module NumberField NumberField.InfinitePlace NumberField.Units

variable (K : Type*) [Field K]

namespace NumberField.Units.dirichletUnitTheorem

/-!
### Dirichlet Unit Theorem

We define a group morphism from `(𝓞 K)ˣ` to `logSpace K`, defined as
`{w : InfinitePlace K // w ≠ w₀} → ℝ` where `w₀` is a distinguished (arbitrary) infinite place,
prove that its kernel is the torsion subgroup (see `logEmbedding_eq_zero_iff`) and that its image,
called `unitLattice`, is a full `ℤ`-lattice. It follows that `unitLattice` is a free `ℤ`-module
(see `instModuleFree_unitLattice`) of rank `card (InfinitePlace K) - 1` (see `unitLattice_rank`).
To prove that the `unitLattice` is a full `ℤ`-lattice, we need to prove that it is discrete
(see `unitLattice_inter_ball_finite`) and that it spans the full space over `ℝ`
(see `unitLattice_span_eq_top`); this is the main part of the proof, see the section `span_top`
below for more details.
-/

open Finset

variable {K}

section NumberField

variable [NumberField K]

def w₀ : InfinitePlace K := (inferInstance : Nonempty (InfinitePlace K)).some

variable (K) in

abbrev logSpace := {w : InfinitePlace K // w ≠ w₀} → ℝ

variable (K) in

def _root_.NumberField.Units.logEmbedding :
    Additive ((𝓞 K)ˣ) →+ logSpace K :=

{ toFun := fun x w ↦ mult w.val * Real.log (w.val ↑x.toMul)

  map_zero' := by simp; rfl

  map_add' := fun _ _ ↦ by simp [Real.log_mul, mul_add]; rfl }
