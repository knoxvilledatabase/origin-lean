/-
Extracted from LinearAlgebra/Matrix/GeneralLinearGroup/FinTwo.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Classification of elements of `GL (Fin 2) R`

Here we classify `2 × 2` matrices over the reals (or more generally over `R` where `R` is a
suitable ring, but `ℝ` is the motivating case), into the following classes:

* scalars
* parabolic elements (`Matrix.IsParabolic`) - one eigenvalue with non-semisimple generalized
  eigenspace
* hyperbolic elements (`Matrix.IsHyperbolic`) - two distinct real eigenvalues
* elliptic elements (`Matrix.IsElliptic`) - two distinct non-real complex eigenvalues

This classification is used (among other places) in classifying the fixed points of elements of
`GL(2, ℝ)⁺` acting on the upper half-plane. See [Wikipedia:SL2(R)#Classification_of_elements]
(https://en.wikipedia.org/wiki/SL2(R)#Classification_of_elements).
-/

open Polynomial

namespace Matrix

section CommRing

variable {R : Type*} [CommRing R] (m : Matrix (Fin 2) (Fin 2) R) (g : GL (Fin 2) R)

def IsParabolic : Prop := m ∉ Set.range (scalar _) ∧ m.discr = 0

variable {m}

section conjugation
