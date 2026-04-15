/-
Extracted from NumberTheory/PythagoreanTriples.lean
Genuine: 5 of 6 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Pythagorean Triples

The main result is the classification of Pythagorean triples. The final result is for general
Pythagorean triples. It follows from the more interesting relatively prime case. We use the
"rational parametrization of the circle" method for the proof. The parametrization maps the point
`(x / z, y / z)` to the slope of the line through `(-1, 0)` and `(x / z, y / z)`. This quickly
shows that `(x / z, y / z) = (2 * m * n / (m ^ 2 + n ^ 2), (m ^ 2 - n ^ 2) / (m ^ 2 + n ^ 2))` where
`m / n` is the slope. In order to identify numerators and denominators we now need results showing
that these are coprime. This is easy except for the prime 2. In order to deal with that we have to
analyze the parity of `x`, `y`, `m` and `n` and eliminate all the impossible cases. This takes up
the bulk of the proof below.
-/

assert_not_exists TwoSidedIdeal

theorem sq_ne_two_fin_zmod_four (z : ZMod 4) : z * z ≠ 2 := by
  change Fin 4 at z
  fin_cases z <;> decide

theorem Int.sq_ne_two_mod_four (z : ℤ) : z * z % 4 ≠ 2 := by
  suffices ¬z * z % (4 : ℕ) = 2 % (4 : ℕ) by exact this
  rw [← ZMod.intCast_eq_intCast_iff']
  simpa using sq_ne_two_fin_zmod_four _

noncomputable section

def PythagoreanTriple (x y z : ℤ) : Prop :=
  x * x + y * y = z * z

theorem pythagoreanTriple_comm {x y z : ℤ} : PythagoreanTriple x y z ↔ PythagoreanTriple y x z := by
  delta PythagoreanTriple
  rw [add_comm]

theorem PythagoreanTriple.zero : PythagoreanTriple 0 0 0 := by
  simp only [PythagoreanTriple, zero_mul, zero_add]

namespace PythagoreanTriple

variable {x y z : ℤ}
