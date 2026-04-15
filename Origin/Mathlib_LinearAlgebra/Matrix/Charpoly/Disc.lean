/-
Extracted from LinearAlgebra/Matrix/Charpoly/Disc.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The discriminant of a matrix
-/

open Polynomial

namespace Matrix

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

noncomputable def discr (A : Matrix n n R) : R := A.charpoly.discr

lemma discr_of_card_eq_two (A : Matrix n n R) (hn : Fintype.card n = 2) :
    A.discr = A.trace ^ 2 - 4 * A.det := by
  nontriviality R
  rw [discr, Polynomial.discr_of_degree_eq_two (by simp; norm_cast)]
  simp [A.charpoly_of_card_eq_two hn]

lemma discr_fin_two (A : Matrix (Fin 2) (Fin 2) R) :
    A.discr = A.trace ^ 2 - 4 * A.det :=
  A.discr_of_card_eq_two <| Fintype.card_fin _
