/-
Extracted from LinearAlgebra/Matrix/Charpoly/Univ.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The universal characteristic polynomial

In this file we define the universal characteristic polynomial `Matrix.charpoly.univ`,
which is the characteristic polynomial of the matrix with entries `Xᵢⱼ`,
and hence has coefficients that are multivariate polynomials.

It is universal in the sense that one obtains the characteristic polynomial of a matrix `M`
by evaluating the coefficients of `univ` at the entries of `M`.

We use it to show that the coefficients of the characteristic polynomial
of a matrix are homogeneous polynomials in the matrix entries.

## Main results

* `Matrix.charpoly.univ`: the universal characteristic polynomial
* `Matrix.charpoly.univ_map_eval₂Hom`: evaluating `univ` on the entries of a matrix `M`
  gives the characteristic polynomial of `M`.
* `Matrix.charpoly.univ_coeff_isHomogeneous`:
  the `i`-th coefficient of `univ` is a homogeneous polynomial of degree `n - i`.
-/

namespace Matrix.charpoly

variable {R S : Type*} (n : Type*) [CommRing R] [CommRing S] [Fintype n] [DecidableEq n]

variable (f : R →+* S)

variable (R) in

noncomputable

abbrev univ : Polynomial (MvPolynomial (n × n) R) :=
  charpoly <| mvPolynomialX n n R

open MvPolynomial RingHomClass in
