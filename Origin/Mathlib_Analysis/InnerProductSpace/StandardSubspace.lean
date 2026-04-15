/-
Extracted from Analysis/InnerProductSpace/StandardSubspace.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Standard subspaces of a Hilbert space

This files defines standard subspaces of a complex Hilbert space: a standard subspace `S` of `H` is
a closed real subspace `S` such that `S ⊓ i S = ⊥` and `S ⊔ i S = ⊤`. For a standard subspace, one
can define a closable operator `x + i y ↦ x - i y` and develop an analogue of the Tomita-Takesaki
modular theory for von Neumann algebras. By considering inclusions of standard subspaces, one can
obtain unitary representations of various Lie groups.

## Main definitions and results

* `instance : InnerProductSpace ℝ H` for `InnerProductSpace ℂ H`, by restricting the scalar product
  to its real part

* `StandardSubspace` as a structure with a `ClosedSubmodule` for `InnerProductSpace ℝ H` satisfying
  `IsCyclic` and `IsSeparating`. Actually the interesting cases need `CompleteSpace H`, but the
  definition is given for a general case.

* `symplComp` as a `StandardSubspace` of the symplectic complement of a standard subspace with
  respect to `⟪⬝, ⬝⟫.im`

* `symplComp_symplComp_eq` the double symplectic complement is equal to itself

## References

* [Chap. 2 of Lecture notes by R. Longo](https://www.mat.uniroma2.it/longo/Lecture-Notes_files/LN-Part1.pdf)

* [Oberwolfach report](https://ems.press/content/serial-article-files/48171)

## TODO

Define the Tomita conjugation, prove Tomita's theorem, prove the KMS condition.
-/

open Complex ContinuousLinearMap

open scoped ComplexInnerProductSpace

section ScalarSMulCLE

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]

set_option backward.isDefEq.respectTransparency false in

noncomputable def scalarSMulCLE (c : ℂˣ) : H ≃L[ℝ] H := ContinuousLinearEquiv.smulLeft c
